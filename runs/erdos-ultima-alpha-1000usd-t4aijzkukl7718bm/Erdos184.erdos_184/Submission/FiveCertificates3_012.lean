import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src2400 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst2400 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle2400_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2400_1 : CycleData E W := ⟨4,![4,19,14,1,20,9],![2,6,27,4,8,18]⟩
def cycle2400_2 : CycleData E W := ⟨3,![2,23,17,11,7],![3,8,38,26,14]⟩
def cycle2400_3 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2400_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2400_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2400 : PartitionData E W := ⟨6,![cycle2400_0,cycle2400_1,cycle2400_2,cycle2400_3,cycle2400_4,cycle2400_5]⟩
lemma valid_data2400 : data2400.Valid src2400 dst2400 Finset.univ := by decide +kernel

def src2401 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst2401 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle2401_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2401_1 : CycleData E W := ⟨4,![4,19,14,1,20,9],![2,6,27,4,8,18]⟩
def cycle2401_2 : CycleData E W := ⟨2,![2,23,12,7],![3,8,28,14]⟩
def cycle2401_3 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2401_4 : CycleData E W := ⟨2,![8,21,17,11],![14,18,38,26]⟩
def cycle2401_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2401 : PartitionData E W := ⟨6,![cycle2401_0,cycle2401_1,cycle2401_2,cycle2401_3,cycle2401_4,cycle2401_5]⟩
lemma valid_data2401 : data2401.Valid src2401 dst2401 Finset.univ := by decide +kernel

def src2402 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst2402 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle2402_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2402_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2402_2 : CycleData E W := ⟨3,![2,23,17,11,7],![3,8,38,26,14]⟩
def cycle2402_3 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2402_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,27,38,18]⟩
def cycle2402_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2402 : PartitionData E W := ⟨6,![cycle2402_0,cycle2402_1,cycle2402_2,cycle2402_3,cycle2402_4,cycle2402_5]⟩
lemma valid_data2402 : data2402.Valid src2402 dst2402 Finset.univ := by decide +kernel

def src2403 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst2403 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle2403_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2403_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2403_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2403_3 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2403_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2403_5 : CycleData E W := ⟨2,![17,13,22,18],![26,27,28,38]⟩
def data2403 : PartitionData E W := ⟨6,![cycle2403_0,cycle2403_1,cycle2403_2,cycle2403_3,cycle2403_4,cycle2403_5]⟩
lemma valid_data2403 : data2403.Valid src2403 dst2403 Finset.univ := by decide +kernel

def src2404 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst2404 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle2404_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2404_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2404_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2404_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2404_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2404_5 : CycleData E W := ⟨2,![17,13,22,18],![26,27,28,38]⟩
def data2404 : PartitionData E W := ⟨6,![cycle2404_0,cycle2404_1,cycle2404_2,cycle2404_3,cycle2404_4,cycle2404_5]⟩
lemma valid_data2404 : data2404.Valid src2404 dst2404 Finset.univ := by decide +kernel

def src2405 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst2405 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle2405_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2405_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2405_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2405_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2405_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2405_5 : CycleData E W := ⟨3,![20,13,17,18,23],![8,28,27,26,38]⟩
def data2405 : PartitionData E W := ⟨6,![cycle2405_0,cycle2405_1,cycle2405_2,cycle2405_3,cycle2405_4,cycle2405_5]⟩
lemma valid_data2405 : data2405.Valid src2405 dst2405 Finset.univ := by decide +kernel

def src2406 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst2406 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle2406_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2406_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2406_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2406_3 : CycleData E W := ⟨4,![4,19,18,23,20,9],![2,6,26,38,8,18]⟩
def cycle2406_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2406_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2406 : PartitionData E W := ⟨6,![cycle2406_0,cycle2406_1,cycle2406_2,cycle2406_3,cycle2406_4,cycle2406_5]⟩
lemma valid_data2406 : data2406.Valid src2406 dst2406 Finset.univ := by decide +kernel

def src2407 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst2407 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle2407_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2407_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2407_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2407_3 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,26,38,18]⟩
def cycle2407_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2407_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2407 : PartitionData E W := ⟨6,![cycle2407_0,cycle2407_1,cycle2407_2,cycle2407_3,cycle2407_4,cycle2407_5]⟩
lemma valid_data2407 : data2407.Valid src2407 dst2407 Finset.univ := by decide +kernel

def src2408 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst2408 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle2408_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2408_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2408_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2408_3 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,26,38,18]⟩
def cycle2408_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2408_5 : CycleData E W := ⟨2,![20,13,17,23],![8,28,27,38]⟩
def data2408 : PartitionData E W := ⟨6,![cycle2408_0,cycle2408_1,cycle2408_2,cycle2408_3,cycle2408_4,cycle2408_5]⟩
lemma valid_data2408 : data2408.Valid src2408 dst2408 Finset.univ := by decide +kernel

def src2409 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst2409 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle2409_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2409_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2409_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2409_3 : CycleData E W := ⟨3,![5,16,23,20,9],![2,16,38,8,18]⟩
def cycle2409_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2409_5 : CycleData E W := ⟨2,![17,22,13,18],![26,38,28,27]⟩
def data2409 : PartitionData E W := ⟨6,![cycle2409_0,cycle2409_1,cycle2409_2,cycle2409_3,cycle2409_4,cycle2409_5]⟩
lemma valid_data2409 : data2409.Valid src2409 dst2409 Finset.univ := by decide +kernel

def src2410 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst2410 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle2410_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2410_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2410_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2410_3 : CycleData E W := ⟨2,![5,16,21,9],![2,16,38,18]⟩
def cycle2410_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2410_5 : CycleData E W := ⟨2,![17,22,13,18],![26,38,28,27]⟩
def data2410 : PartitionData E W := ⟨6,![cycle2410_0,cycle2410_1,cycle2410_2,cycle2410_3,cycle2410_4,cycle2410_5]⟩
lemma valid_data2410 : data2410.Valid src2410 dst2410 Finset.univ := by decide +kernel

def src2411 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst2411 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle2411_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2411_1 : CycleData E W := ⟨3,![2,1,10,11,7],![3,8,4,26,14]⟩
def cycle2411_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2411_3 : CycleData E W := ⟨2,![5,16,22,9],![2,16,38,18]⟩
def cycle2411_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2411_5 : CycleData E W := ⟨3,![20,13,18,17,23],![8,28,27,26,38]⟩
def data2411 : PartitionData E W := ⟨6,![cycle2411_0,cycle2411_1,cycle2411_2,cycle2411_3,cycle2411_4,cycle2411_5]⟩
lemma valid_data2411 : data2411.Valid src2411 dst2411 Finset.univ := by decide +kernel

def src2412 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2412 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2412_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2412_1 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2412_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2412_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2412_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2412_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2412 : PartitionData E W := ⟨6,![cycle2412_0,cycle2412_1,cycle2412_2,cycle2412_3,cycle2412_4,cycle2412_5]⟩
lemma valid_data2412 : data2412.Valid src2412 dst2412 Finset.univ := by decide +kernel

def src2413 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2413 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2413_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2413_1 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2413_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2413_3 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2413_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2413_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2413 : PartitionData E W := ⟨6,![cycle2413_0,cycle2413_1,cycle2413_2,cycle2413_3,cycle2413_4,cycle2413_5]⟩
lemma valid_data2413 : data2413.Valid src2413 dst2413 Finset.univ := by decide +kernel

def src2414 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2414 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2414_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2414_1 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2414_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2414_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2414_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2414_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2414 : PartitionData E W := ⟨6,![cycle2414_0,cycle2414_1,cycle2414_2,cycle2414_3,cycle2414_4,cycle2414_5]⟩
lemma valid_data2414 : data2414.Valid src2414 dst2414 Finset.univ := by decide +kernel

def src2415 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst2415 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle2415_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2415_1 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2415_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2415_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2415_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2415_5 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data2415 : PartitionData E W := ⟨6,![cycle2415_0,cycle2415_1,cycle2415_2,cycle2415_3,cycle2415_4,cycle2415_5]⟩
lemma valid_data2415 : data2415.Valid src2415 dst2415 Finset.univ := by decide +kernel

def src2416 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst2416 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle2416_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2416_1 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2416_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2416_3 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2416_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2416_5 : CycleData E W := ⟨2,![17,13,22,18],![16,27,28,38]⟩
def data2416 : PartitionData E W := ⟨6,![cycle2416_0,cycle2416_1,cycle2416_2,cycle2416_3,cycle2416_4,cycle2416_5]⟩
lemma valid_data2416 : data2416.Valid src2416 dst2416 Finset.univ := by decide +kernel

def src2417 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst2417 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle2417_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2417_1 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2417_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2417_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2417_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2417_5 : CycleData E W := ⟨3,![20,13,17,18,23],![8,28,27,16,38]⟩
def data2417 : PartitionData E W := ⟨6,![cycle2417_0,cycle2417_1,cycle2417_2,cycle2417_3,cycle2417_4,cycle2417_5]⟩
lemma valid_data2417 : data2417.Valid src2417 dst2417 Finset.univ := by decide +kernel

def src2418 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2418 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2418_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2418_1 : CycleData E W := ⟨2,![1,23,16,10],![4,8,38,26]⟩
def cycle2418_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2418_3 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2418_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2418_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2418 : PartitionData E W := ⟨6,![cycle2418_0,cycle2418_1,cycle2418_2,cycle2418_3,cycle2418_4,cycle2418_5]⟩
lemma valid_data2418 : data2418.Valid src2418 dst2418 Finset.univ := by decide +kernel

def src2419 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2419 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2419_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2419_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2419_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2419_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2419_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2419_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data2419 : PartitionData E W := ⟨6,![cycle2419_0,cycle2419_1,cycle2419_2,cycle2419_3,cycle2419_4,cycle2419_5]⟩
lemma valid_data2419 : data2419.Valid src2419 dst2419 Finset.univ := by decide +kernel

def src2420 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2420 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2420_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2420_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2420_2 : CycleData E W := ⟨3,![2,23,16,11,7],![3,8,38,26,14]⟩
def cycle2420_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2420_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2420_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2420 : PartitionData E W := ⟨6,![cycle2420_0,cycle2420_1,cycle2420_2,cycle2420_3,cycle2420_4,cycle2420_5]⟩
lemma valid_data2420 : data2420.Valid src2420 dst2420 Finset.univ := by decide +kernel

def src2421 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2421 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2421_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2421_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2421_2 : CycleData E W := ⟨3,![4,3,2,20,9],![2,6,3,8,18]⟩
def cycle2421_3 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle2421_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2421_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2421 : PartitionData E W := ⟨6,![cycle2421_0,cycle2421_1,cycle2421_2,cycle2421_3,cycle2421_4,cycle2421_5]⟩
lemma valid_data2421 : data2421.Valid src2421 dst2421 Finset.univ := by decide +kernel

def src2422 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2422 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2422_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,26,16]⟩
def cycle2422_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2422_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2422_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,27,16]⟩
def cycle2422_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2422_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data2422 : PartitionData E W := ⟨6,![cycle2422_0,cycle2422_1,cycle2422_2,cycle2422_3,cycle2422_4,cycle2422_5]⟩
lemma valid_data2422 : data2422.Valid src2422 dst2422 Finset.univ := by decide +kernel

def src2423 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2423 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2423_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2423_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2423_2 : CycleData E W := ⟨3,![2,20,13,15,3],![3,8,28,27,6]⟩
def cycle2423_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2423_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,26,14]⟩
def cycle2423_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2423 : PartitionData E W := ⟨6,![cycle2423_0,cycle2423_1,cycle2423_2,cycle2423_3,cycle2423_4,cycle2423_5]⟩
lemma valid_data2423 : data2423.Valid src2423 dst2423 Finset.univ := by decide +kernel

def src2424 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst2424 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle2424_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2424_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2424_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2424_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2424_4 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle2424_5 : CycleData E W := ⟨2,![16,11,18,17],![16,26,27,38]⟩
def data2424 : PartitionData E W := ⟨6,![cycle2424_0,cycle2424_1,cycle2424_2,cycle2424_3,cycle2424_4,cycle2424_5]⟩
lemma valid_data2424 : data2424.Valid src2424 dst2424 Finset.univ := by decide +kernel

def src2425 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst2425 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle2425_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2425_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2425_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2425_3 : CycleData E W := ⟨3,![3,19,11,16,6],![3,6,27,26,16]⟩
def cycle2425_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2425_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data2425 : PartitionData E W := ⟨6,![cycle2425_0,cycle2425_1,cycle2425_2,cycle2425_3,cycle2425_4,cycle2425_5]⟩
lemma valid_data2425 : data2425.Valid src2425 dst2425 Finset.univ := by decide +kernel

def src2426 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst2426 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle2426_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2426_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2426_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2426_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2426_4 : CycleData E W := ⟨4,![5,16,11,18,22,9],![2,16,26,27,38,18]⟩
def cycle2426_5 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def data2426 : PartitionData E W := ⟨6,![cycle2426_0,cycle2426_1,cycle2426_2,cycle2426_3,cycle2426_4,cycle2426_5]⟩
lemma valid_data2426 : data2426.Valid src2426 dst2426 Finset.univ := by decide +kernel

def src2427 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst2427 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle2427_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2427_1 : CycleData E W := ⟨2,![3,15,12,7],![3,6,27,14]⟩
def cycle2427_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2427_3 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle2427_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2427_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2427 : PartitionData E W := ⟨6,![cycle2427_0,cycle2427_1,cycle2427_2,cycle2427_3,cycle2427_4,cycle2427_5]⟩
lemma valid_data2427 : data2427.Valid src2427 dst2427 Finset.univ := by decide +kernel

def src2428 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst2428 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle2428_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2428_1 : CycleData E W := ⟨2,![3,15,12,7],![3,6,27,14]⟩
def cycle2428_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2428_3 : CycleData E W := ⟨2,![20,8,13,23],![8,18,14,28]⟩
def cycle2428_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2428_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2428 : PartitionData E W := ⟨6,![cycle2428_0,cycle2428_1,cycle2428_2,cycle2428_3,cycle2428_4,cycle2428_5]⟩
lemma valid_data2428 : data2428.Valid src2428 dst2428 Finset.univ := by decide +kernel

def src2429 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst2429 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle2429_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2429_1 : CycleData E W := ⟨2,![3,15,12,7],![3,6,27,14]⟩
def cycle2429_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2429_3 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle2429_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,26,38,8,28]⟩
def cycle2429_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2429 : PartitionData E W := ⟨6,![cycle2429_0,cycle2429_1,cycle2429_2,cycle2429_3,cycle2429_4,cycle2429_5]⟩
lemma valid_data2429 : data2429.Valid src2429 dst2429 Finset.univ := by decide +kernel

def src2430 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst2430 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle2430_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2430_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2430_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2430_3 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2430_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2430_5 : CycleData E W := ⟨2,![11,22,18,17],![26,28,38,27]⟩
def data2430 : PartitionData E W := ⟨6,![cycle2430_0,cycle2430_1,cycle2430_2,cycle2430_3,cycle2430_4,cycle2430_5]⟩
lemma valid_data2430 : data2430.Valid src2430 dst2430 Finset.univ := by decide +kernel

def src2431 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst2431 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle2431_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2431_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2431_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2431_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2431_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2431_5 : CycleData E W := ⟨2,![11,22,18,17],![26,28,38,27]⟩
def data2431 : PartitionData E W := ⟨6,![cycle2431_0,cycle2431_1,cycle2431_2,cycle2431_3,cycle2431_4,cycle2431_5]⟩
lemma valid_data2431 : data2431.Valid src2431 dst2431 Finset.univ := by decide +kernel

def src2432 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst2432 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle2432_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2432_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2432_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2432_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2432_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2432_5 : CycleData E W := ⟨3,![20,11,17,18,23],![8,28,26,27,38]⟩
def data2432 : PartitionData E W := ⟨6,![cycle2432_0,cycle2432_1,cycle2432_2,cycle2432_3,cycle2432_4,cycle2432_5]⟩
lemma valid_data2432 : data2432.Valid src2432 dst2432 Finset.univ := by decide +kernel

def src2433 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst2433 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle2433_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2433_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2433_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2433_3 : CycleData E W := ⟨4,![4,19,18,23,20,9],![2,6,27,38,8,18]⟩
def cycle2433_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2433_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2433 : PartitionData E W := ⟨6,![cycle2433_0,cycle2433_1,cycle2433_2,cycle2433_3,cycle2433_4,cycle2433_5]⟩
lemma valid_data2433 : data2433.Valid src2433 dst2433 Finset.univ := by decide +kernel

def src2434 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst2434 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle2434_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2434_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2434_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2434_3 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2434_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2434_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2434 : PartitionData E W := ⟨6,![cycle2434_0,cycle2434_1,cycle2434_2,cycle2434_3,cycle2434_4,cycle2434_5]⟩
lemma valid_data2434 : data2434.Valid src2434 dst2434 Finset.univ := by decide +kernel

def src2435 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst2435 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle2435_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2435_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2435_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2435_3 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,27,38,18]⟩
def cycle2435_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2435_5 : CycleData E W := ⟨2,![20,11,17,23],![8,28,26,38]⟩
def data2435 : PartitionData E W := ⟨6,![cycle2435_0,cycle2435_1,cycle2435_2,cycle2435_3,cycle2435_4,cycle2435_5]⟩
lemma valid_data2435 : data2435.Valid src2435 dst2435 Finset.univ := by decide +kernel

def src2436 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst2436 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle2436_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2436_1 : CycleData E W := ⟨4,![4,19,10,1,20,9],![2,6,26,4,8,18]⟩
def cycle2436_2 : CycleData E W := ⟨3,![2,23,17,13,7],![3,8,38,27,14]⟩
def cycle2436_3 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2436_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2436_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2436 : PartitionData E W := ⟨6,![cycle2436_0,cycle2436_1,cycle2436_2,cycle2436_3,cycle2436_4,cycle2436_5]⟩
lemma valid_data2436 : data2436.Valid src2436 dst2436 Finset.univ := by decide +kernel

def src2437 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst2437 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle2437_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2437_1 : CycleData E W := ⟨4,![4,19,10,1,20,9],![2,6,26,4,8,18]⟩
def cycle2437_2 : CycleData E W := ⟨2,![2,23,12,7],![3,8,28,14]⟩
def cycle2437_3 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2437_4 : CycleData E W := ⟨2,![8,21,17,13],![14,18,38,27]⟩
def cycle2437_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2437 : PartitionData E W := ⟨6,![cycle2437_0,cycle2437_1,cycle2437_2,cycle2437_3,cycle2437_4,cycle2437_5]⟩
lemma valid_data2437 : data2437.Valid src2437 dst2437 Finset.univ := by decide +kernel

def src2438 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst2438 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle2438_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2438_1 : CycleData E W := ⟨2,![1,20,11,10],![4,8,28,26]⟩
def cycle2438_2 : CycleData E W := ⟨3,![2,23,17,13,7],![3,8,38,27,14]⟩
def cycle2438_3 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2438_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,26,38,18]⟩
def cycle2438_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2438 : PartitionData E W := ⟨6,![cycle2438_0,cycle2438_1,cycle2438_2,cycle2438_3,cycle2438_4,cycle2438_5]⟩
lemma valid_data2438 : data2438.Valid src2438 dst2438 Finset.univ := by decide +kernel

def src2439 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst2439 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle2439_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,26,6]⟩
def cycle2439_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2439_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2439_3 : CycleData E W := ⟨3,![5,16,23,20,9],![2,16,38,8,18]⟩
def cycle2439_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2439_5 : CycleData E W := ⟨2,![11,22,17,18],![26,28,38,27]⟩
def data2439 : PartitionData E W := ⟨6,![cycle2439_0,cycle2439_1,cycle2439_2,cycle2439_3,cycle2439_4,cycle2439_5]⟩
lemma valid_data2439 : data2439.Valid src2439 dst2439 Finset.univ := by decide +kernel

def src2440 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst2440 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle2440_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,26,6]⟩
def cycle2440_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2440_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2440_3 : CycleData E W := ⟨2,![5,16,21,9],![2,16,38,18]⟩
def cycle2440_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2440_5 : CycleData E W := ⟨2,![11,22,17,18],![26,28,38,27]⟩
def data2440 : PartitionData E W := ⟨6,![cycle2440_0,cycle2440_1,cycle2440_2,cycle2440_3,cycle2440_4,cycle2440_5]⟩
lemma valid_data2440 : data2440.Valid src2440 dst2440 Finset.univ := by decide +kernel

def src2441 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst2441 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle2441_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,26,6]⟩
def cycle2441_1 : CycleData E W := ⟨3,![2,1,14,13,7],![3,8,4,27,14]⟩
def cycle2441_2 : CycleData E W := ⟨1,![3,15,6],![3,6,16]⟩
def cycle2441_3 : CycleData E W := ⟨2,![5,16,22,9],![2,16,38,18]⟩
def cycle2441_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2441_5 : CycleData E W := ⟨3,![20,11,18,17,23],![8,28,26,27,38]⟩
def data2441 : PartitionData E W := ⟨6,![cycle2441_0,cycle2441_1,cycle2441_2,cycle2441_3,cycle2441_4,cycle2441_5]⟩
lemma valid_data2441 : data2441.Valid src2441 dst2441 Finset.univ := by decide +kernel

def src2442 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2442 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2442_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2442_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2442_2 : CycleData E W := ⟨3,![4,3,2,20,9],![2,6,3,8,18]⟩
def cycle2442_3 : CycleData E W := ⟨2,![6,17,13,7],![3,16,27,14]⟩
def cycle2442_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2442_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2442 : PartitionData E W := ⟨6,![cycle2442_0,cycle2442_1,cycle2442_2,cycle2442_3,cycle2442_4,cycle2442_5]⟩
lemma valid_data2442 : data2442.Valid src2442 dst2442 Finset.univ := by decide +kernel

def src2443 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2443 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2443_0 : CycleData E W := ⟨2,![0,14,17,5],![2,4,27,16]⟩
def cycle2443_1 : CycleData E W := ⟨2,![1,23,11,10],![4,8,28,26]⟩
def cycle2443_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2443_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2443_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2443_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2443 : PartitionData E W := ⟨6,![cycle2443_0,cycle2443_1,cycle2443_2,cycle2443_3,cycle2443_4,cycle2443_5]⟩
lemma valid_data2443 : data2443.Valid src2443 dst2443 Finset.univ := by decide +kernel

def src2444 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2444 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2444_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2444_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2444_2 : CycleData E W := ⟨3,![2,20,11,15,3],![3,8,28,26,6]⟩
def cycle2444_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2444_4 : CycleData E W := ⟨2,![6,17,13,7],![3,16,27,14]⟩
def cycle2444_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2444 : PartitionData E W := ⟨6,![cycle2444_0,cycle2444_1,cycle2444_2,cycle2444_3,cycle2444_4,cycle2444_5]⟩
lemma valid_data2444 : data2444.Valid src2444 dst2444 Finset.univ := by decide +kernel

def src2445 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2445 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2445_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2445_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2445_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,16,3,8,18]⟩
def cycle2445_3 : CycleData E W := ⟨2,![3,19,13,7],![3,6,27,14]⟩
def cycle2445_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2445_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data2445 : PartitionData E W := ⟨6,![cycle2445_0,cycle2445_1,cycle2445_2,cycle2445_3,cycle2445_4,cycle2445_5]⟩
lemma valid_data2445 : data2445.Valid src2445 dst2445 Finset.univ := by decide +kernel

def src2446 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2446 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2446_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2446_1 : CycleData E W := ⟨2,![1,23,11,10],![4,8,28,26]⟩
def cycle2446_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2446_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2446_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2446_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2446 : PartitionData E W := ⟨6,![cycle2446_0,cycle2446_1,cycle2446_2,cycle2446_3,cycle2446_4,cycle2446_5]⟩
lemma valid_data2446 : data2446.Valid src2446 dst2446 Finset.univ := by decide +kernel

def src2447 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2447 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2447_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2447_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2447_2 : CycleData E W := ⟨3,![2,20,11,16,6],![3,8,28,26,16]⟩
def cycle2447_3 : CycleData E W := ⟨2,![3,19,13,7],![3,6,27,14]⟩
def cycle2447_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2447_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2447 : PartitionData E W := ⟨6,![cycle2447_0,cycle2447_1,cycle2447_2,cycle2447_3,cycle2447_4,cycle2447_5]⟩
lemma valid_data2447 : data2447.Valid src2447 dst2447 Finset.univ := by decide +kernel

def src2448 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2448 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2448_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2448_1 : CycleData E W := ⟨2,![3,15,13,7],![3,6,27,14]⟩
def cycle2448_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2448_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2448_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2448_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2448 : PartitionData E W := ⟨6,![cycle2448_0,cycle2448_1,cycle2448_2,cycle2448_3,cycle2448_4,cycle2448_5]⟩
lemma valid_data2448 : data2448.Valid src2448 dst2448 Finset.univ := by decide +kernel

def src2449 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2449 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2449_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2449_1 : CycleData E W := ⟨2,![3,15,13,7],![3,6,27,14]⟩
def cycle2449_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2449_3 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2449_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2449_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2449 : PartitionData E W := ⟨6,![cycle2449_0,cycle2449_1,cycle2449_2,cycle2449_3,cycle2449_4,cycle2449_5]⟩
lemma valid_data2449 : data2449.Valid src2449 dst2449 Finset.univ := by decide +kernel

def src2450 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2450 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2450_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2450_1 : CycleData E W := ⟨2,![3,15,13,7],![3,6,27,14]⟩
def cycle2450_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2450_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2450_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2450_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data2450 : PartitionData E W := ⟨6,![cycle2450_0,cycle2450_1,cycle2450_2,cycle2450_3,cycle2450_4,cycle2450_5]⟩
lemma valid_data2450 : data2450.Valid src2450 dst2450 Finset.univ := by decide +kernel

def src2451 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst2451 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle2451_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2451_1 : CycleData E W := ⟨2,![3,15,13,7],![3,6,27,14]⟩
def cycle2451_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2451_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2451_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2451_5 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data2451 : PartitionData E W := ⟨6,![cycle2451_0,cycle2451_1,cycle2451_2,cycle2451_3,cycle2451_4,cycle2451_5]⟩
lemma valid_data2451 : data2451.Valid src2451 dst2451 Finset.univ := by decide +kernel

def src2452 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst2452 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle2452_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2452_1 : CycleData E W := ⟨2,![3,15,13,7],![3,6,27,14]⟩
def cycle2452_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2452_3 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2452_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2452_5 : CycleData E W := ⟨2,![17,11,22,18],![16,26,28,38]⟩
def data2452 : PartitionData E W := ⟨6,![cycle2452_0,cycle2452_1,cycle2452_2,cycle2452_3,cycle2452_4,cycle2452_5]⟩
lemma valid_data2452 : data2452.Valid src2452 dst2452 Finset.univ := by decide +kernel

def src2453 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst2453 : E → W := ![4,8,3,6,2,16,3,14,18,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle2453_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2453_1 : CycleData E W := ⟨2,![3,15,13,7],![3,6,27,14]⟩
def cycle2453_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2453_3 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2453_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2453_5 : CycleData E W := ⟨3,![20,11,17,18,23],![8,28,26,16,38]⟩
def data2453 : PartitionData E W := ⟨6,![cycle2453_0,cycle2453_1,cycle2453_2,cycle2453_3,cycle2453_4,cycle2453_5]⟩
lemma valid_data2453 : data2453.Valid src2453 dst2453 Finset.univ := by decide +kernel

def src2454 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst2454 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle2454_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2454_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2454_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2454_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2454_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,26,14]⟩
def cycle2454_5 : CycleData E W := ⟨2,![13,22,18,17],![26,28,38,27]⟩
def data2454 : PartitionData E W := ⟨6,![cycle2454_0,cycle2454_1,cycle2454_2,cycle2454_3,cycle2454_4,cycle2454_5]⟩
lemma valid_data2454 : data2454.Valid src2454 dst2454 Finset.univ := by decide +kernel

def src2455 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst2455 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle2455_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2455_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2455_2 : CycleData E W := ⟨3,![2,20,21,19,3],![3,8,18,38,6]⟩
def cycle2455_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2455_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,26,14]⟩
def cycle2455_5 : CycleData E W := ⟨2,![13,22,18,17],![26,28,38,27]⟩
def data2455 : PartitionData E W := ⟨6,![cycle2455_0,cycle2455_1,cycle2455_2,cycle2455_3,cycle2455_4,cycle2455_5]⟩
lemma valid_data2455 : data2455.Valid src2455 dst2455 Finset.univ := by decide +kernel

def src2456 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst2456 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle2456_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2456_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2456_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2456_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2456_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,26,14]⟩
def cycle2456_5 : CycleData E W := ⟨3,![21,13,17,18,22],![18,28,26,27,38]⟩
def data2456 : PartitionData E W := ⟨6,![cycle2456_0,cycle2456_1,cycle2456_2,cycle2456_3,cycle2456_4,cycle2456_5]⟩
lemma valid_data2456 : data2456.Valid src2456 dst2456 Finset.univ := by decide +kernel

def src2457 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst2457 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle2457_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2457_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2457_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,27,6]⟩
def cycle2457_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2457_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,26,14]⟩
def cycle2457_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2457 : PartitionData E W := ⟨6,![cycle2457_0,cycle2457_1,cycle2457_2,cycle2457_3,cycle2457_4,cycle2457_5]⟩
lemma valid_data2457 : data2457.Valid src2457 dst2457 Finset.univ := by decide +kernel

def src2458 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst2458 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle2458_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2458_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2458_2 : CycleData E W := ⟨4,![2,20,21,18,19,3],![3,8,18,38,27,6]⟩
def cycle2458_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2458_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,26,14]⟩
def cycle2458_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2458 : PartitionData E W := ⟨6,![cycle2458_0,cycle2458_1,cycle2458_2,cycle2458_3,cycle2458_4,cycle2458_5]⟩
lemma valid_data2458 : data2458.Valid src2458 dst2458 Finset.univ := by decide +kernel

def src2459 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst2459 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle2459_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2459_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2459_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,27,6]⟩
def cycle2459_3 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2459_4 : CycleData E W := ⟨2,![6,16,12,7],![3,16,26,14]⟩
def cycle2459_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,26,38]⟩
def data2459 : PartitionData E W := ⟨6,![cycle2459_0,cycle2459_1,cycle2459_2,cycle2459_3,cycle2459_4,cycle2459_5]⟩
lemma valid_data2459 : data2459.Valid src2459 dst2459 Finset.univ := by decide +kernel

def src2460 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst2460 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle2460_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2460_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2460_2 : CycleData E W := ⟨3,![2,23,17,16,6],![3,8,38,27,16]⟩
def cycle2460_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,26,14]⟩
def cycle2460_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2460_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2460 : PartitionData E W := ⟨6,![cycle2460_0,cycle2460_1,cycle2460_2,cycle2460_3,cycle2460_4,cycle2460_5]⟩
lemma valid_data2460 : data2460.Valid src2460 dst2460 Finset.univ := by decide +kernel

def src2461 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst2461 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle2461_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2461_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2461_2 : CycleData E W := ⟨4,![2,20,21,17,16,6],![3,8,18,38,27,16]⟩
def cycle2461_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,26,14]⟩
def cycle2461_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2461_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2461 : PartitionData E W := ⟨6,![cycle2461_0,cycle2461_1,cycle2461_2,cycle2461_3,cycle2461_4,cycle2461_5]⟩
lemma valid_data2461 : data2461.Valid src2461 dst2461 Finset.univ := by decide +kernel

def src2462 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst2462 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle2462_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2462_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2462_2 : CycleData E W := ⟨3,![2,23,17,16,6],![3,8,38,27,16]⟩
def cycle2462_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,26,14]⟩
def cycle2462_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2462_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data2462 : PartitionData E W := ⟨6,![cycle2462_0,cycle2462_1,cycle2462_2,cycle2462_3,cycle2462_4,cycle2462_5]⟩
lemma valid_data2462 : data2462.Valid src2462 dst2462 Finset.univ := by decide +kernel

def src2463 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst2463 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle2463_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2463_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2463_2 : CycleData E W := ⟨2,![2,23,16,6],![3,8,38,16]⟩
def cycle2463_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,26,14]⟩
def cycle2463_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2463_5 : CycleData E W := ⟨2,![13,22,17,18],![26,28,38,27]⟩
def data2463 : PartitionData E W := ⟨6,![cycle2463_0,cycle2463_1,cycle2463_2,cycle2463_3,cycle2463_4,cycle2463_5]⟩
lemma valid_data2463 : data2463.Valid src2463 dst2463 Finset.univ := by decide +kernel

def src2464 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst2464 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle2464_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2464_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2464_2 : CycleData E W := ⟨3,![2,20,21,16,6],![3,8,18,38,16]⟩
def cycle2464_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,26,14]⟩
def cycle2464_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2464_5 : CycleData E W := ⟨2,![13,22,17,18],![26,28,38,27]⟩
def data2464 : PartitionData E W := ⟨6,![cycle2464_0,cycle2464_1,cycle2464_2,cycle2464_3,cycle2464_4,cycle2464_5]⟩
lemma valid_data2464 : data2464.Valid src2464 dst2464 Finset.univ := by decide +kernel

def src2465 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst2465 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle2465_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2465_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2465_2 : CycleData E W := ⟨2,![2,23,16,6],![3,8,38,16]⟩
def cycle2465_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,26,14]⟩
def cycle2465_4 : CycleData E W := ⟨1,![4,15,5],![2,6,16]⟩
def cycle2465_5 : CycleData E W := ⟨3,![21,13,18,17,22],![18,28,26,27,38]⟩
def data2465 : PartitionData E W := ⟨6,![cycle2465_0,cycle2465_1,cycle2465_2,cycle2465_3,cycle2465_4,cycle2465_5]⟩
lemma valid_data2465 : data2465.Valid src2465 dst2465 Finset.univ := by decide +kernel

def src2466 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2466 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2466_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2466_1 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2466_2 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2466_3 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle2466_4 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,26]⟩
def cycle2466_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data2466 : PartitionData E W := ⟨6,![cycle2466_0,cycle2466_1,cycle2466_2,cycle2466_3,cycle2466_4,cycle2466_5]⟩
lemma valid_data2466 : data2466.Valid src2466 dst2466 Finset.univ := by decide +kernel

def src2467 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2467 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2467_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,27,16]⟩
def cycle2467_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2467_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2467_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2467_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2467_5 : CycleData E W := ⟨3,![11,18,22,13,12],![14,27,38,28,26]⟩
def data2467 : PartitionData E W := ⟨6,![cycle2467_0,cycle2467_1,cycle2467_2,cycle2467_3,cycle2467_4,cycle2467_5]⟩
lemma valid_data2467 : data2467.Valid src2467 dst2467 Finset.univ := by decide +kernel

def src2468 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2468 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2468_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,27,16]⟩
def cycle2468_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2468_2 : CycleData E W := ⟨3,![2,23,18,11,7],![3,8,38,27,14]⟩
def cycle2468_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2468_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2468_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,26]⟩
def data2468 : PartitionData E W := ⟨6,![cycle2468_0,cycle2468_1,cycle2468_2,cycle2468_3,cycle2468_4,cycle2468_5]⟩
lemma valid_data2468 : data2468.Valid src2468 dst2468 Finset.univ := by decide +kernel

def src2469 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2469 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2469_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2469_1 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2469_2 : CycleData E W := ⟨2,![3,19,11,7],![3,6,27,14]⟩
def cycle2469_3 : CycleData E W := ⟨2,![4,15,16,5],![2,6,26,16]⟩
def cycle2469_4 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,26]⟩
def cycle2469_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data2469 : PartitionData E W := ⟨6,![cycle2469_0,cycle2469_1,cycle2469_2,cycle2469_3,cycle2469_4,cycle2469_5]⟩
lemma valid_data2469 : data2469.Valid src2469 dst2469 Finset.univ := by decide +kernel

def src2470 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2470 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2470_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,27,6]⟩
def cycle2470_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2470_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2470_3 : CycleData E W := ⟨2,![3,15,16,6],![3,6,26,16]⟩
def cycle2470_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2470_5 : CycleData E W := ⟨3,![11,18,22,13,12],![14,27,38,28,26]⟩
def data2470 : PartitionData E W := ⟨6,![cycle2470_0,cycle2470_1,cycle2470_2,cycle2470_3,cycle2470_4,cycle2470_5]⟩
lemma valid_data2470 : data2470.Valid src2470 dst2470 Finset.univ := by decide +kernel

def src2471 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2471 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2471_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,27,6]⟩
def cycle2471_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2471_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2471_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2471_4 : CycleData E W := ⟨3,![5,16,13,21,9],![2,16,26,28,18]⟩
def cycle2471_5 : CycleData E W := ⟨2,![8,22,18,11],![14,18,38,27]⟩
def data2471 : PartitionData E W := ⟨6,![cycle2471_0,cycle2471_1,cycle2471_2,cycle2471_3,cycle2471_4,cycle2471_5]⟩
lemma valid_data2471 : data2471.Valid src2471 dst2471 Finset.univ := by decide +kernel

def src2472 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst2472 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle2472_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,27,16]⟩
def cycle2472_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2472_2 : CycleData E W := ⟨2,![2,23,18,6],![3,8,38,16]⟩
def cycle2472_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,14,18]⟩
def cycle2472_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2472_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2472 : PartitionData E W := ⟨6,![cycle2472_0,cycle2472_1,cycle2472_2,cycle2472_3,cycle2472_4,cycle2472_5]⟩
lemma valid_data2472 : data2472.Valid src2472 dst2472 Finset.univ := by decide +kernel

def src2473 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst2473 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle2473_0 : CycleData E W := ⟨2,![0,10,17,5],![2,4,27,16]⟩
def cycle2473_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2473_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2473_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,38,16]⟩
def cycle2473_4 : CycleData E W := ⟨4,![4,15,13,22,21,9],![2,6,26,28,38,18]⟩
def cycle2473_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def data2473 : PartitionData E W := ⟨6,![cycle2473_0,cycle2473_1,cycle2473_2,cycle2473_3,cycle2473_4,cycle2473_5]⟩
lemma valid_data2473 : data2473.Valid src2473 dst2473 Finset.univ := by decide +kernel

def src2474 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst2474 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle2474_0 : CycleData E W := ⟨3,![0,10,16,15,4],![2,4,27,26,6]⟩
def cycle2474_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2474_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2474_3 : CycleData E W := ⟨2,![5,18,22,9],![2,16,38,18]⟩
def cycle2474_4 : CycleData E W := ⟨2,![6,17,11,7],![3,16,27,14]⟩
def cycle2474_5 : CycleData E W := ⟨2,![8,21,13,12],![14,18,28,26]⟩
def data2474 : PartitionData E W := ⟨6,![cycle2474_0,cycle2474_1,cycle2474_2,cycle2474_3,cycle2474_4,cycle2474_5]⟩
lemma valid_data2474 : data2474.Valid src2474 dst2474 Finset.univ := by decide +kernel

def src2475 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2475 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2475_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2475_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2475_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2475_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2475_4 : CycleData E W := ⟨2,![4,19,18,5],![2,6,27,16]⟩
def cycle2475_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2475 : PartitionData E W := ⟨6,![cycle2475_0,cycle2475_1,cycle2475_2,cycle2475_3,cycle2475_4,cycle2475_5]⟩
lemma valid_data2475 : data2475.Valid src2475 dst2475 Finset.univ := by decide +kernel

def src2476 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2476 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2476_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2476_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2476_2 : CycleData E W := ⟨3,![2,20,21,17,6],![3,8,18,38,16]⟩
def cycle2476_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2476_4 : CycleData E W := ⟨2,![4,19,18,5],![2,6,27,16]⟩
def cycle2476_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2476 : PartitionData E W := ⟨6,![cycle2476_0,cycle2476_1,cycle2476_2,cycle2476_3,cycle2476_4,cycle2476_5]⟩
lemma valid_data2476 : data2476.Valid src2476 dst2476 Finset.univ := by decide +kernel

def src2477 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2477 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2477_0 : CycleData E W := ⟨3,![0,10,11,8,9],![2,4,27,14,18]⟩
def cycle2477_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2477_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2477_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2477_4 : CycleData E W := ⟨2,![4,19,18,5],![2,6,27,16]⟩
def cycle2477_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2477 : PartitionData E W := ⟨6,![cycle2477_0,cycle2477_1,cycle2477_2,cycle2477_3,cycle2477_4,cycle2477_5]⟩
lemma valid_data2477 : data2477.Valid src2477 dst2477 Finset.univ := by decide +kernel

def src2478 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst2478 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle2478_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2478_1 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2478_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2478_3 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle2478_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2478_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2478 : PartitionData E W := ⟨6,![cycle2478_0,cycle2478_1,cycle2478_2,cycle2478_3,cycle2478_4,cycle2478_5]⟩
lemma valid_data2478 : data2478.Valid src2478 dst2478 Finset.univ := by decide +kernel

def src2479 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst2479 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle2479_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2479_1 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2479_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2479_3 : CycleData E W := ⟨2,![20,8,13,23],![8,18,14,28]⟩
def cycle2479_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2479_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2479 : PartitionData E W := ⟨6,![cycle2479_0,cycle2479_1,cycle2479_2,cycle2479_3,cycle2479_4,cycle2479_5]⟩
lemma valid_data2479 : data2479.Valid src2479 dst2479 Finset.univ := by decide +kernel

def src2480 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst2480 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle2480_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,16]⟩
def cycle2480_1 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2480_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2480_3 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def cycle2480_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,27,38,8,28]⟩
def cycle2480_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2480 : PartitionData E W := ⟨6,![cycle2480_0,cycle2480_1,cycle2480_2,cycle2480_3,cycle2480_4,cycle2480_5]⟩
lemma valid_data2480 : data2480.Valid src2480 dst2480 Finset.univ := by decide +kernel

def src2481 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst2481 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle2481_0 : CycleData E W := ⟨2,![0,10,18,5],![2,4,27,16]⟩
def cycle2481_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2481_2 : CycleData E W := ⟨2,![2,23,17,6],![3,8,38,16]⟩
def cycle2481_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,14,18]⟩
def cycle2481_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2481_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2481 : PartitionData E W := ⟨6,![cycle2481_0,cycle2481_1,cycle2481_2,cycle2481_3,cycle2481_4,cycle2481_5]⟩
lemma valid_data2481 : data2481.Valid src2481 dst2481 Finset.univ := by decide +kernel

def src2482 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst2482 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle2482_0 : CycleData E W := ⟨3,![0,10,11,15,4],![2,4,27,26,6]⟩
def cycle2482_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2482_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,14]⟩
def cycle2482_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2482_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2482_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2482 : PartitionData E W := ⟨6,![cycle2482_0,cycle2482_1,cycle2482_2,cycle2482_3,cycle2482_4,cycle2482_5]⟩
lemma valid_data2482 : data2482.Valid src2482 dst2482 Finset.univ := by decide +kernel

def src2483 : E → W := ![2,4,8,3,6,2,16,3,14,18,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst2483 : E → W := ![4,8,3,6,2,16,3,14,18,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle2483_0 : CycleData E W := ⟨3,![0,10,11,15,4],![2,4,27,26,6]⟩
def cycle2483_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2483_2 : CycleData E W := ⟨3,![2,23,16,12,7],![3,8,38,26,14]⟩
def cycle2483_3 : CycleData E W := ⟨2,![3,19,18,6],![3,6,27,16]⟩
def cycle2483_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2483_5 : CycleData E W := ⟨1,![8,21,13],![14,18,28]⟩
def data2483 : PartitionData E W := ⟨6,![cycle2483_0,cycle2483_1,cycle2483_2,cycle2483_3,cycle2483_4,cycle2483_5]⟩
lemma valid_data2483 : data2483.Valid src2483 dst2483 Finset.univ := by decide +kernel

def src2484 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2484 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2484_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2484_1 : CycleData E W := ⟨3,![2,1,14,21,8],![3,8,4,28,18]⟩
def cycle2484_2 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2484_3 : CycleData E W := ⟨3,![5,17,23,20,9],![2,16,38,8,18]⟩
def cycle2484_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2484_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2484 : PartitionData E W := ⟨6,![cycle2484_0,cycle2484_1,cycle2484_2,cycle2484_3,cycle2484_4,cycle2484_5]⟩
lemma valid_data2484 : data2484.Valid src2484 dst2484 Finset.univ := by decide +kernel

def src2485 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2485 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2485_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2485_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2485_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2485_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2485_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2485_5 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2485_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2485 : PartitionData E W := ⟨7,![cycle2485_0,cycle2485_1,cycle2485_2,cycle2485_3,cycle2485_4,cycle2485_5,cycle2485_6]⟩
lemma valid_data2485 : data2485.Valid src2485 dst2485 Finset.univ := by decide +kernel

def src2486 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2486 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2486_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2486_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2486_2 : CycleData E W := ⟨4,![5,17,23,2,8,9],![2,16,38,8,3,18]⟩
def cycle2486_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2486_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2486_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2486 : PartitionData E W := ⟨6,![cycle2486_0,cycle2486_1,cycle2486_2,cycle2486_3,cycle2486_4,cycle2486_5]⟩
lemma valid_data2486 : data2486.Valid src2486 dst2486 Finset.univ := by decide +kernel

def src2487 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2487 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2487_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2487_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2487_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2487_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2487_4 : CycleData E W := ⟨3,![5,18,13,21,9],![2,16,27,28,18]⟩
def cycle2487_5 : CycleData E W := ⟨2,![6,17,16,11],![14,16,38,26]⟩
def data2487 : PartitionData E W := ⟨6,![cycle2487_0,cycle2487_1,cycle2487_2,cycle2487_3,cycle2487_4,cycle2487_5]⟩
lemma valid_data2487 : data2487.Valid src2487 dst2487 Finset.univ := by decide +kernel

def src2488 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2488 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2488_0 : CycleData E W := ⟨3,![0,10,11,6,5],![2,4,26,14,16]⟩
def cycle2488_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2488_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2488_3 : CycleData E W := ⟨2,![3,19,12,7],![3,6,27,14]⟩
def cycle2488_4 : CycleData E W := ⟨3,![4,15,16,21,9],![2,6,26,38,18]⟩
def cycle2488_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2488 : PartitionData E W := ⟨6,![cycle2488_0,cycle2488_1,cycle2488_2,cycle2488_3,cycle2488_4,cycle2488_5]⟩
lemma valid_data2488 : data2488.Valid src2488 dst2488 Finset.univ := by decide +kernel

def src2489 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2489 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2489_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2489_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2489_2 : CycleData E W := ⟨3,![2,23,16,11,7],![3,8,38,26,14]⟩
def cycle2489_3 : CycleData E W := ⟨3,![3,19,13,21,8],![3,6,27,28,18]⟩
def cycle2489_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2489_5 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def data2489 : PartitionData E W := ⟨6,![cycle2489_0,cycle2489_1,cycle2489_2,cycle2489_3,cycle2489_4,cycle2489_5]⟩
lemma valid_data2489 : data2489.Valid src2489 dst2489 Finset.univ := by decide +kernel

def src2490 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2490 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2490_0 : CycleData E W := ⟨3,![0,14,13,16,5],![2,4,28,27,16]⟩
def cycle2490_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2490_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2490_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,27,14]⟩
def cycle2490_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2490_5 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def data2490 : PartitionData E W := ⟨6,![cycle2490_0,cycle2490_1,cycle2490_2,cycle2490_3,cycle2490_4,cycle2490_5]⟩
lemma valid_data2490 : data2490.Valid src2490 dst2490 Finset.univ := by decide +kernel

def src2491 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2491 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2491_0 : CycleData E W := ⟨3,![0,10,11,6,5],![2,4,26,14,16]⟩
def cycle2491_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2491_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2491_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,27,14]⟩
def cycle2491_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2491_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,27,28,38,26]⟩
def data2491 : PartitionData E W := ⟨6,![cycle2491_0,cycle2491_1,cycle2491_2,cycle2491_3,cycle2491_4,cycle2491_5]⟩
lemma valid_data2491 : data2491.Valid src2491 dst2491 Finset.univ := by decide +kernel

def src2492 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2492 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2492_0 : CycleData E W := ⟨3,![0,14,13,16,5],![2,4,28,27,16]⟩
def cycle2492_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2492_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2492_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,27,14]⟩
def cycle2492_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2492_5 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def data2492 : PartitionData E W := ⟨6,![cycle2492_0,cycle2492_1,cycle2492_2,cycle2492_3,cycle2492_4,cycle2492_5]⟩
lemma valid_data2492 : data2492.Valid src2492 dst2492 Finset.univ := by decide +kernel

def src2493 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2493 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2493_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2493_1 : CycleData E W := ⟨4,![5,17,14,1,20,9],![2,16,27,4,8,18]⟩
def cycle2493_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2493_3 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2493_4 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def cycle2493_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2493 : PartitionData E W := ⟨6,![cycle2493_0,cycle2493_1,cycle2493_2,cycle2493_3,cycle2493_4,cycle2493_5]⟩
lemma valid_data2493 : data2493.Valid src2493 dst2493 Finset.univ := by decide +kernel

def src2494 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2494 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2494_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2494_1 : CycleData E W := ⟨4,![5,17,14,1,20,9],![2,16,27,4,8,18]⟩
def cycle2494_2 : CycleData E W := ⟨2,![2,23,12,7],![3,8,28,14]⟩
def cycle2494_3 : CycleData E W := ⟨2,![3,19,21,8],![3,6,38,18]⟩
def cycle2494_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2494_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2494 : PartitionData E W := ⟨6,![cycle2494_0,cycle2494_1,cycle2494_2,cycle2494_3,cycle2494_4,cycle2494_5]⟩
lemma valid_data2494 : data2494.Valid src2494 dst2494 Finset.univ := by decide +kernel

def src2495 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2495 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2495_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2495_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2495_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2495_3 : CycleData E W := ⟨3,![5,17,18,22,9],![2,16,27,38,18]⟩
def cycle2495_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2495_5 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def data2495 : PartitionData E W := ⟨6,![cycle2495_0,cycle2495_1,cycle2495_2,cycle2495_3,cycle2495_4,cycle2495_5]⟩
lemma valid_data2495 : data2495.Valid src2495 dst2495 Finset.univ := by decide +kernel

def src2496 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2496 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2496_0 : CycleData E W := ⟨2,![0,14,18,5],![2,4,27,16]⟩
def cycle2496_1 : CycleData E W := ⟨2,![1,23,16,10],![4,8,38,26]⟩
def cycle2496_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2496_3 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2496_4 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2496_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data2496 : PartitionData E W := ⟨6,![cycle2496_0,cycle2496_1,cycle2496_2,cycle2496_3,cycle2496_4,cycle2496_5]⟩
lemma valid_data2496 : data2496.Valid src2496 dst2496 Finset.univ := by decide +kernel

def src2497 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2497 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2497_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2497_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2497_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2497_3 : CycleData E W := ⟨3,![3,19,18,6,7],![3,6,27,16,14]⟩
def cycle2497_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2497_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data2497 : PartitionData E W := ⟨6,![cycle2497_0,cycle2497_1,cycle2497_2,cycle2497_3,cycle2497_4,cycle2497_5]⟩
lemma valid_data2497 : data2497.Valid src2497 dst2497 Finset.univ := by decide +kernel

def src2498 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2498 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2498_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2498_1 : CycleData E W := ⟨2,![1,23,16,10],![4,8,38,26]⟩
def cycle2498_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2498_3 : CycleData E W := ⟨2,![3,15,11,7],![3,6,26,14]⟩
def cycle2498_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2498_5 : CycleData E W := ⟨2,![6,18,13,12],![14,16,27,28]⟩
def data2498 : PartitionData E W := ⟨6,![cycle2498_0,cycle2498_1,cycle2498_2,cycle2498_3,cycle2498_4,cycle2498_5]⟩
lemma valid_data2498 : data2498.Valid src2498 dst2498 Finset.univ := by decide +kernel

def src2499 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2499 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2499_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2499_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2499_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2499_3 : CycleData E W := ⟨3,![3,19,22,12,7],![3,6,38,28,14]⟩
def cycle2499_4 : CycleData E W := ⟨3,![5,16,13,21,9],![2,16,27,28,18]⟩
def cycle2499_5 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def data2499 : PartitionData E W := ⟨6,![cycle2499_0,cycle2499_1,cycle2499_2,cycle2499_3,cycle2499_4,cycle2499_5]⟩
lemma valid_data2499 : data2499.Valid src2499 dst2499 Finset.univ := by decide +kernel

def src2500 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2500 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2500_0 : CycleData E W := ⟨2,![0,14,16,5],![2,4,27,16]⟩
def cycle2500_1 : CycleData E W := ⟨3,![1,20,21,18,10],![4,8,18,38,26]⟩
def cycle2500_2 : CycleData E W := ⟨2,![2,23,12,7],![3,8,28,14]⟩
def cycle2500_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2500_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle2500_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2500 : PartitionData E W := ⟨6,![cycle2500_0,cycle2500_1,cycle2500_2,cycle2500_3,cycle2500_4,cycle2500_5]⟩
lemma valid_data2500 : data2500.Valid src2500 dst2500 Finset.univ := by decide +kernel

def src2501 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2501 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2501_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2501_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2501_2 : CycleData E W := ⟨2,![2,20,12,7],![3,8,28,14]⟩
def cycle2501_3 : CycleData E W := ⟨2,![3,19,22,8],![3,6,38,18]⟩
def cycle2501_4 : CycleData E W := ⟨3,![5,16,13,21,9],![2,16,27,28,18]⟩
def cycle2501_5 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def data2501 : PartitionData E W := ⟨6,![cycle2501_0,cycle2501_1,cycle2501_2,cycle2501_3,cycle2501_4,cycle2501_5]⟩
lemma valid_data2501 : data2501.Valid src2501 dst2501 Finset.univ := by decide +kernel

def src2502 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2502 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2502_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2502_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2502_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2502_3 : CycleData E W := ⟨3,![3,19,22,12,7],![3,6,38,28,14]⟩
def cycle2502_4 : CycleData E W := ⟨3,![5,16,11,21,9],![2,16,26,28,18]⟩
def cycle2502_5 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def data2502 : PartitionData E W := ⟨6,![cycle2502_0,cycle2502_1,cycle2502_2,cycle2502_3,cycle2502_4,cycle2502_5]⟩
lemma valid_data2502 : data2502.Valid src2502 dst2502 Finset.univ := by decide +kernel

def src2503 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2503 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2503_0 : CycleData E W := ⟨2,![0,10,16,5],![2,4,26,16]⟩
def cycle2503_1 : CycleData E W := ⟨3,![1,20,21,18,14],![4,8,18,38,27]⟩
def cycle2503_2 : CycleData E W := ⟨2,![2,23,12,7],![3,8,28,14]⟩
def cycle2503_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2503_4 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle2503_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2503 : PartitionData E W := ⟨6,![cycle2503_0,cycle2503_1,cycle2503_2,cycle2503_3,cycle2503_4,cycle2503_5]⟩
lemma valid_data2503 : data2503.Valid src2503 dst2503 Finset.univ := by decide +kernel

def src2504 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2504 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2504_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2504_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2504_2 : CycleData E W := ⟨2,![2,20,12,7],![3,8,28,14]⟩
def cycle2504_3 : CycleData E W := ⟨2,![3,19,22,8],![3,6,38,18]⟩
def cycle2504_4 : CycleData E W := ⟨3,![5,16,11,21,9],![2,16,26,28,18]⟩
def cycle2504_5 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def data2504 : PartitionData E W := ⟨6,![cycle2504_0,cycle2504_1,cycle2504_2,cycle2504_3,cycle2504_4,cycle2504_5]⟩
lemma valid_data2504 : data2504.Valid src2504 dst2504 Finset.univ := by decide +kernel

def src2505 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2505 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2505_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2505_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2505_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2505_3 : CycleData E W := ⟨2,![3,19,13,7],![3,6,27,14]⟩
def cycle2505_4 : CycleData E W := ⟨3,![5,6,12,21,9],![2,16,14,28,18]⟩
def cycle2505_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data2505 : PartitionData E W := ⟨6,![cycle2505_0,cycle2505_1,cycle2505_2,cycle2505_3,cycle2505_4,cycle2505_5]⟩
lemma valid_data2505 : data2505.Valid src2505 dst2505 Finset.univ := by decide +kernel

def src2506 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2506 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2506_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2506_1 : CycleData E W := ⟨3,![1,23,22,18,14],![4,8,28,38,27]⟩
def cycle2506_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2506_3 : CycleData E W := ⟨2,![3,19,13,7],![3,6,27,14]⟩
def cycle2506_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2506_5 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def data2506 : PartitionData E W := ⟨6,![cycle2506_0,cycle2506_1,cycle2506_2,cycle2506_3,cycle2506_4,cycle2506_5]⟩
lemma valid_data2506 : data2506.Valid src2506 dst2506 Finset.univ := by decide +kernel

def src2507 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2507 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2507_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2507_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2507_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2507_3 : CycleData E W := ⟨2,![3,19,13,7],![3,6,27,14]⟩
def cycle2507_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2507_5 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def data2507 : PartitionData E W := ⟨6,![cycle2507_0,cycle2507_1,cycle2507_2,cycle2507_3,cycle2507_4,cycle2507_5]⟩
lemma valid_data2507 : data2507.Valid src2507 dst2507 Finset.univ := by decide +kernel

def src2508 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2508 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2508_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2508_1 : CycleData E W := ⟨4,![5,17,10,1,20,9],![2,16,26,4,8,18]⟩
def cycle2508_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2508_3 : CycleData E W := ⟨1,![6,16,13],![14,16,27]⟩
def cycle2508_4 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def cycle2508_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2508 : PartitionData E W := ⟨6,![cycle2508_0,cycle2508_1,cycle2508_2,cycle2508_3,cycle2508_4,cycle2508_5]⟩
lemma valid_data2508 : data2508.Valid src2508 dst2508 Finset.univ := by decide +kernel

def src2509 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2509 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2509_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2509_1 : CycleData E W := ⟨4,![5,17,10,1,20,9],![2,16,26,4,8,18]⟩
def cycle2509_2 : CycleData E W := ⟨2,![2,23,12,7],![3,8,28,14]⟩
def cycle2509_3 : CycleData E W := ⟨2,![3,19,21,8],![3,6,38,18]⟩
def cycle2509_4 : CycleData E W := ⟨1,![6,16,13],![14,16,27]⟩
def cycle2509_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2509 : PartitionData E W := ⟨6,![cycle2509_0,cycle2509_1,cycle2509_2,cycle2509_3,cycle2509_4,cycle2509_5]⟩
lemma valid_data2509 : data2509.Valid src2509 dst2509 Finset.univ := by decide +kernel

def src2510 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2510 : E → W := ![4,8,3,6,2,16,14,3,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2510_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2510_1 : CycleData E W := ⟨2,![1,20,11,10],![4,8,28,26]⟩
def cycle2510_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2510_3 : CycleData E W := ⟨3,![5,17,18,22,9],![2,16,26,38,18]⟩
def cycle2510_4 : CycleData E W := ⟨1,![6,16,13],![14,16,27]⟩
def cycle2510_5 : CycleData E W := ⟨2,![7,12,21,8],![3,14,28,18]⟩
def data2510 : PartitionData E W := ⟨6,![cycle2510_0,cycle2510_1,cycle2510_2,cycle2510_3,cycle2510_4,cycle2510_5]⟩
lemma valid_data2510 : data2510.Valid src2510 dst2510 Finset.univ := by decide +kernel

def src2511 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2511 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2511_0 : CycleData E W := ⟨3,![0,14,13,16,5],![2,4,28,26,16]⟩
def cycle2511_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,27]⟩
def cycle2511_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2511_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2511_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2511_5 : CycleData E W := ⟨1,![6,17,11],![14,16,27]⟩
def data2511 : PartitionData E W := ⟨6,![cycle2511_0,cycle2511_1,cycle2511_2,cycle2511_3,cycle2511_4,cycle2511_5]⟩
lemma valid_data2511 : data2511.Valid src2511 dst2511 Finset.univ := by decide +kernel

def src2512 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2512 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2512_0 : CycleData E W := ⟨3,![0,10,11,6,5],![2,4,27,14,16]⟩
def cycle2512_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2512_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2512_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2512_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2512_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,26,28,38,27]⟩
def data2512 : PartitionData E W := ⟨6,![cycle2512_0,cycle2512_1,cycle2512_2,cycle2512_3,cycle2512_4,cycle2512_5]⟩
lemma valid_data2512 : data2512.Valid src2512 dst2512 Finset.univ := by decide +kernel

def src2513 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2513 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2513_0 : CycleData E W := ⟨3,![0,14,13,16,5],![2,4,28,26,16]⟩
def cycle2513_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,27]⟩
def cycle2513_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2513_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2513_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2513_5 : CycleData E W := ⟨1,![6,17,11],![14,16,27]⟩
def data2513 : PartitionData E W := ⟨6,![cycle2513_0,cycle2513_1,cycle2513_2,cycle2513_3,cycle2513_4,cycle2513_5]⟩
lemma valid_data2513 : data2513.Valid src2513 dst2513 Finset.univ := by decide +kernel

def src2514 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2514 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2514_0 : CycleData E W := ⟨3,![0,14,13,15,4],![2,4,28,26,6]⟩
def cycle2514_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,27]⟩
def cycle2514_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2514_3 : CycleData E W := ⟨2,![3,19,11,7],![3,6,27,14]⟩
def cycle2514_4 : CycleData E W := ⟨3,![5,17,22,21,9],![2,16,38,28,18]⟩
def cycle2514_5 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def data2514 : PartitionData E W := ⟨6,![cycle2514_0,cycle2514_1,cycle2514_2,cycle2514_3,cycle2514_4,cycle2514_5]⟩
lemma valid_data2514 : data2514.Valid src2514 dst2514 Finset.univ := by decide +kernel

def src2515 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2515 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2515_0 : CycleData E W := ⟨3,![0,10,11,6,5],![2,4,27,14,16]⟩
def cycle2515_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2515_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2515_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2515_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2515_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2515 : PartitionData E W := ⟨6,![cycle2515_0,cycle2515_1,cycle2515_2,cycle2515_3,cycle2515_4,cycle2515_5]⟩
lemma valid_data2515 : data2515.Valid src2515 dst2515 Finset.univ := by decide +kernel

def src2516 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2516 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2516_0 : CycleData E W := ⟨3,![0,14,13,15,4],![2,4,28,26,6]⟩
def cycle2516_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,27]⟩
def cycle2516_2 : CycleData E W := ⟨2,![2,20,21,8],![3,8,28,18]⟩
def cycle2516_3 : CycleData E W := ⟨2,![3,19,11,7],![3,6,27,14]⟩
def cycle2516_4 : CycleData E W := ⟨2,![5,17,22,9],![2,16,38,18]⟩
def cycle2516_5 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def data2516 : PartitionData E W := ⟨6,![cycle2516_0,cycle2516_1,cycle2516_2,cycle2516_3,cycle2516_4,cycle2516_5]⟩
lemma valid_data2516 : data2516.Valid src2516 dst2516 Finset.univ := by decide +kernel

def src2517 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2517 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2517_0 : CycleData E W := ⟨2,![0,10,18,5],![2,4,27,16]⟩
def cycle2517_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2517_2 : CycleData E W := ⟨3,![2,23,17,6,7],![3,8,38,16,14]⟩
def cycle2517_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2517_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2517_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2517 : PartitionData E W := ⟨6,![cycle2517_0,cycle2517_1,cycle2517_2,cycle2517_3,cycle2517_4,cycle2517_5]⟩
lemma valid_data2517 : data2517.Valid src2517 dst2517 Finset.univ := by decide +kernel

def src2518 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2518 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2518_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,27,6]⟩
def cycle2518_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2518_2 : CycleData E W := ⟨1,![2,20,8],![3,8,18]⟩
def cycle2518_3 : CycleData E W := ⟨2,![3,15,12,7],![3,6,26,14]⟩
def cycle2518_4 : CycleData E W := ⟨2,![5,17,21,9],![2,16,38,18]⟩
def cycle2518_5 : CycleData E W := ⟨1,![6,18,11],![14,16,27]⟩
def cycle2518_6 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2518 : PartitionData E W := ⟨7,![cycle2518_0,cycle2518_1,cycle2518_2,cycle2518_3,cycle2518_4,cycle2518_5,cycle2518_6]⟩
lemma valid_data2518 : data2518.Valid src2518 dst2518 Finset.univ := by decide +kernel

def src2519 : E → W := ![2,4,8,3,6,2,16,14,3,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2519 : E → W := ![4,8,3,6,2,16,14,3,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2519_0 : CycleData E W := ⟨2,![0,10,18,5],![2,4,27,16]⟩
def cycle2519_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2519_2 : CycleData E W := ⟨3,![2,23,17,6,7],![3,8,38,16,14]⟩
def cycle2519_3 : CycleData E W := ⟨2,![4,3,8,9],![2,6,3,18]⟩
def cycle2519_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2519_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2519 : PartitionData E W := ⟨6,![cycle2519_0,cycle2519_1,cycle2519_2,cycle2519_3,cycle2519_4,cycle2519_5]⟩
lemma valid_data2519 : data2519.Valid src2519 dst2519 Finset.univ := by decide +kernel

def src2520 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2520 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2520_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2520_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2520_2 : CycleData E W := ⟨4,![4,3,14,21,8,9],![2,8,4,28,18,14]⟩
def cycle2520_3 : CycleData E W := ⟨2,![20,7,17,23],![8,18,16,38]⟩
def cycle2520_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2520_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2520 : PartitionData E W := ⟨6,![cycle2520_0,cycle2520_1,cycle2520_2,cycle2520_3,cycle2520_4,cycle2520_5]⟩
lemma valid_data2520 : data2520.Valid src2520 dst2520 Finset.univ := by decide +kernel

def src2521 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2521 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2521_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2521_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2521_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2521_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2521_4 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2521_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2521_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2521 : PartitionData E W := ⟨7,![cycle2521_0,cycle2521_1,cycle2521_2,cycle2521_3,cycle2521_4,cycle2521_5,cycle2521_6]⟩
lemma valid_data2521 : data2521.Valid src2521 dst2521 Finset.univ := by decide +kernel

def src2522 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2522 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2522_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2522_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2522_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2522_3 : CycleData E W := ⟨4,![4,23,17,7,8,9],![2,8,38,16,18,14]⟩
def cycle2522_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2522_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2522 : PartitionData E W := ⟨6,![cycle2522_0,cycle2522_1,cycle2522_2,cycle2522_3,cycle2522_4,cycle2522_5]⟩
lemma valid_data2522 : data2522.Valid src2522 dst2522 Finset.univ := by decide +kernel

def src2523 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2523 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2523_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2523_1 : CycleData E W := ⟨3,![2,10,16,17,6],![3,4,26,38,16]⟩
def cycle2523_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2523_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2523_4 : CycleData E W := ⟨2,![7,21,13,18],![16,18,28,27]⟩
def cycle2523_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2523 : PartitionData E W := ⟨6,![cycle2523_0,cycle2523_1,cycle2523_2,cycle2523_3,cycle2523_4,cycle2523_5]⟩
lemma valid_data2523 : data2523.Valid src2523 dst2523 Finset.univ := by decide +kernel

def src2524 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2524 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2524_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2524_1 : CycleData E W := ⟨3,![2,10,16,17,6],![3,4,26,38,16]⟩
def cycle2524_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2524_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2524_4 : CycleData E W := ⟨3,![7,21,22,13,18],![16,18,38,28,27]⟩
def cycle2524_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2524 : PartitionData E W := ⟨6,![cycle2524_0,cycle2524_1,cycle2524_2,cycle2524_3,cycle2524_4,cycle2524_5]⟩
lemma valid_data2524 : data2524.Valid src2524 dst2524 Finset.univ := by decide +kernel

def src2525 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2525 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2525_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2525_1 : CycleData E W := ⟨3,![2,10,16,17,6],![3,4,26,38,16]⟩
def cycle2525_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2525_3 : CycleData E W := ⟨3,![4,23,22,8,9],![2,8,38,18,14]⟩
def cycle2525_4 : CycleData E W := ⟨2,![7,21,13,18],![16,18,28,27]⟩
def cycle2525_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2525 : PartitionData E W := ⟨6,![cycle2525_0,cycle2525_1,cycle2525_2,cycle2525_3,cycle2525_4,cycle2525_5]⟩
lemma valid_data2525 : data2525.Valid src2525 dst2525 Finset.univ := by decide +kernel

def src2526 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2526 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2526_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2526_1 : CycleData E W := ⟨2,![2,10,17,6],![3,4,26,16]⟩
def cycle2526_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2526_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,26,14]⟩
def cycle2526_4 : CycleData E W := ⟨2,![8,7,16,12],![14,18,16,27]⟩
def cycle2526_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2526 : PartitionData E W := ⟨6,![cycle2526_0,cycle2526_1,cycle2526_2,cycle2526_3,cycle2526_4,cycle2526_5]⟩
lemma valid_data2526 : data2526.Valid src2526 dst2526 Finset.univ := by decide +kernel

def src2527 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2527 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2527_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2527_1 : CycleData E W := ⟨4,![2,10,11,12,16,6],![3,4,26,14,27,16]⟩
def cycle2527_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2527_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2527_4 : CycleData E W := ⟨2,![7,21,18,17],![16,18,38,26]⟩
def cycle2527_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2527 : PartitionData E W := ⟨6,![cycle2527_0,cycle2527_1,cycle2527_2,cycle2527_3,cycle2527_4,cycle2527_5]⟩
lemma valid_data2527 : data2527.Valid src2527 dst2527 Finset.univ := by decide +kernel

def src2528 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2528 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2528_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2528_1 : CycleData E W := ⟨2,![2,10,17,6],![3,4,26,16]⟩
def cycle2528_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2528_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,26,14]⟩
def cycle2528_4 : CycleData E W := ⟨2,![8,7,16,12],![14,18,16,27]⟩
def cycle2528_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2528 : PartitionData E W := ⟨6,![cycle2528_0,cycle2528_1,cycle2528_2,cycle2528_3,cycle2528_4,cycle2528_5]⟩
lemma valid_data2528 : data2528.Valid src2528 dst2528 Finset.univ := by decide +kernel

def src2529 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2529 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2529_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2529_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2529_2 : CycleData E W := ⟨3,![3,20,7,17,14],![4,8,18,16,27]⟩
def cycle2529_3 : CycleData E W := ⟨4,![4,23,19,15,11,9],![2,8,38,6,26,14]⟩
def cycle2529_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2529_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2529 : PartitionData E W := ⟨6,![cycle2529_0,cycle2529_1,cycle2529_2,cycle2529_3,cycle2529_4,cycle2529_5]⟩
lemma valid_data2529 : data2529.Valid src2529 dst2529 Finset.univ := by decide +kernel

def src2530 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2530 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2530_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2530_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2530_2 : CycleData E W := ⟨3,![3,20,7,17,14],![4,8,18,16,27]⟩
def cycle2530_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2530_4 : CycleData E W := ⟨3,![15,11,8,21,19],![6,26,14,18,38]⟩
def cycle2530_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2530 : PartitionData E W := ⟨6,![cycle2530_0,cycle2530_1,cycle2530_2,cycle2530_3,cycle2530_4,cycle2530_5]⟩
lemma valid_data2530 : data2530.Valid src2530 dst2530 Finset.univ := by decide +kernel

def src2531 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2531 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2531_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2531_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2531_2 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle2531_3 : CycleData E W := ⟨4,![4,23,19,15,11,9],![2,8,38,6,26,14]⟩
def cycle2531_4 : CycleData E W := ⟨2,![7,22,18,17],![16,18,38,27]⟩
def cycle2531_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2531 : PartitionData E W := ⟨6,![cycle2531_0,cycle2531_1,cycle2531_2,cycle2531_3,cycle2531_4,cycle2531_5]⟩
lemma valid_data2531 : data2531.Valid src2531 dst2531 Finset.univ := by decide +kernel

def src2532 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2532 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2532_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2532_1 : CycleData E W := ⟨2,![2,14,18,6],![3,4,27,16]⟩
def cycle2532_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,26,14]⟩
def cycle2532_3 : CycleData E W := ⟨2,![20,7,17,23],![8,18,16,38]⟩
def cycle2532_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2532_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data2532 : PartitionData E W := ⟨6,![cycle2532_0,cycle2532_1,cycle2532_2,cycle2532_3,cycle2532_4,cycle2532_5]⟩
lemma valid_data2532 : data2532.Valid src2532 dst2532 Finset.univ := by decide +kernel

def src2533 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2533 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2533_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2533_1 : CycleData E W := ⟨2,![2,14,18,6],![3,4,27,16]⟩
def cycle2533_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,26,14]⟩
def cycle2533_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2533_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2533_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data2533 : PartitionData E W := ⟨6,![cycle2533_0,cycle2533_1,cycle2533_2,cycle2533_3,cycle2533_4,cycle2533_5]⟩
lemma valid_data2533 : data2533.Valid src2533 dst2533 Finset.univ := by decide +kernel

def src2534 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2534 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2534_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2534_1 : CycleData E W := ⟨2,![2,14,18,6],![3,4,27,16]⟩
def cycle2534_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,26,14]⟩
def cycle2534_3 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2534_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2534_5 : CycleData E W := ⟨4,![15,16,23,20,13,19],![6,26,38,8,28,27]⟩
def data2534 : PartitionData E W := ⟨6,![cycle2534_0,cycle2534_1,cycle2534_2,cycle2534_3,cycle2534_4,cycle2534_5]⟩
lemma valid_data2534 : data2534.Valid src2534 dst2534 Finset.univ := by decide +kernel

def src2535 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2535 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2535_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2535_1 : CycleData E W := ⟨2,![2,14,16,6],![3,4,27,16]⟩
def cycle2535_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,26,14]⟩
def cycle2535_3 : CycleData E W := ⟨3,![20,7,17,18,23],![8,18,16,26,38]⟩
def cycle2535_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2535_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2535 : PartitionData E W := ⟨6,![cycle2535_0,cycle2535_1,cycle2535_2,cycle2535_3,cycle2535_4,cycle2535_5]⟩
lemma valid_data2535 : data2535.Valid src2535 dst2535 Finset.univ := by decide +kernel

def src2536 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2536 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2536_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2536_1 : CycleData E W := ⟨2,![2,14,16,6],![3,4,27,16]⟩
def cycle2536_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,26,14]⟩
def cycle2536_3 : CycleData E W := ⟨2,![7,21,18,17],![16,18,38,26]⟩
def cycle2536_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2536_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2536 : PartitionData E W := ⟨6,![cycle2536_0,cycle2536_1,cycle2536_2,cycle2536_3,cycle2536_4,cycle2536_5]⟩
lemma valid_data2536 : data2536.Valid src2536 dst2536 Finset.univ := by decide +kernel

def src2537 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2537 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2537_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2537_1 : CycleData E W := ⟨2,![2,14,16,6],![3,4,27,16]⟩
def cycle2537_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,26,14]⟩
def cycle2537_3 : CycleData E W := ⟨2,![7,22,18,17],![16,18,38,26]⟩
def cycle2537_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2537_5 : CycleData E W := ⟨3,![15,13,20,23,19],![6,27,28,8,38]⟩
def data2537 : PartitionData E W := ⟨6,![cycle2537_0,cycle2537_1,cycle2537_2,cycle2537_3,cycle2537_4,cycle2537_5]⟩
lemma valid_data2537 : data2537.Valid src2537 dst2537 Finset.univ := by decide +kernel

def src2538 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2538 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2538_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2538_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2538_2 : CycleData E W := ⟨3,![4,3,14,13,9],![2,8,4,27,14]⟩
def cycle2538_3 : CycleData E W := ⟨3,![20,7,17,18,23],![8,18,16,27,38]⟩
def cycle2538_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2538_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2538 : PartitionData E W := ⟨6,![cycle2538_0,cycle2538_1,cycle2538_2,cycle2538_3,cycle2538_4,cycle2538_5]⟩
lemma valid_data2538 : data2538.Valid src2538 dst2538 Finset.univ := by decide +kernel

def src2539 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2539 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2539_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2539_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2539_2 : CycleData E W := ⟨3,![4,3,14,13,9],![2,8,4,27,14]⟩
def cycle2539_3 : CycleData E W := ⟨2,![7,21,18,17],![16,18,38,27]⟩
def cycle2539_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2539_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2539 : PartitionData E W := ⟨6,![cycle2539_0,cycle2539_1,cycle2539_2,cycle2539_3,cycle2539_4,cycle2539_5]⟩
lemma valid_data2539 : data2539.Valid src2539 dst2539 Finset.univ := by decide +kernel

def src2540 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2540 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2540_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2540_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2540_2 : CycleData E W := ⟨3,![4,3,14,13,9],![2,8,4,27,14]⟩
def cycle2540_3 : CycleData E W := ⟨2,![7,22,18,17],![16,18,38,27]⟩
def cycle2540_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2540_5 : CycleData E W := ⟨3,![15,11,20,23,19],![6,26,28,8,38]⟩
def data2540 : PartitionData E W := ⟨6,![cycle2540_0,cycle2540_1,cycle2540_2,cycle2540_3,cycle2540_4,cycle2540_5]⟩
lemma valid_data2540 : data2540.Valid src2540 dst2540 Finset.univ := by decide +kernel

def src2541 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2541 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2541_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2541_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2541_2 : CycleData E W := ⟨3,![4,3,14,13,9],![2,8,4,27,14]⟩
def cycle2541_3 : CycleData E W := ⟨2,![20,7,17,23],![8,18,16,38]⟩
def cycle2541_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2541_5 : CycleData E W := ⟨3,![15,11,22,18,19],![6,26,28,38,27]⟩
def data2541 : PartitionData E W := ⟨6,![cycle2541_0,cycle2541_1,cycle2541_2,cycle2541_3,cycle2541_4,cycle2541_5]⟩
lemma valid_data2541 : data2541.Valid src2541 dst2541 Finset.univ := by decide +kernel

def src2542 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2542 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2542_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2542_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2542_2 : CycleData E W := ⟨3,![4,3,14,13,9],![2,8,4,27,14]⟩
def cycle2542_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2542_4 : CycleData E W := ⟨2,![20,8,12,23],![8,18,14,28]⟩
def cycle2542_5 : CycleData E W := ⟨3,![15,11,22,18,19],![6,26,28,38,27]⟩
def data2542 : PartitionData E W := ⟨6,![cycle2542_0,cycle2542_1,cycle2542_2,cycle2542_3,cycle2542_4,cycle2542_5]⟩
lemma valid_data2542 : data2542.Valid src2542 dst2542 Finset.univ := by decide +kernel

def src2543 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2543 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2543_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2543_1 : CycleData E W := ⟨2,![2,10,16,6],![3,4,26,16]⟩
def cycle2543_2 : CycleData E W := ⟨3,![4,3,14,13,9],![2,8,4,27,14]⟩
def cycle2543_3 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2543_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2543_5 : CycleData E W := ⟨4,![15,11,20,23,18,19],![6,26,28,8,38,27]⟩
def data2543 : PartitionData E W := ⟨6,![cycle2543_0,cycle2543_1,cycle2543_2,cycle2543_3,cycle2543_4,cycle2543_5]⟩
lemma valid_data2543 : data2543.Valid src2543 dst2543 Finset.univ := by decide +kernel

def src2544 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2544 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2544_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2544_1 : CycleData E W := ⟨2,![2,14,16,6],![3,4,27,16]⟩
def cycle2544_2 : CycleData E W := ⟨3,![3,20,7,17,10],![4,8,18,16,26]⟩
def cycle2544_3 : CycleData E W := ⟨4,![4,23,19,15,13,9],![2,8,38,6,27,14]⟩
def cycle2544_4 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def cycle2544_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2544 : PartitionData E W := ⟨6,![cycle2544_0,cycle2544_1,cycle2544_2,cycle2544_3,cycle2544_4,cycle2544_5]⟩
lemma valid_data2544 : data2544.Valid src2544 dst2544 Finset.univ := by decide +kernel

def src2545 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2545 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2545_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2545_1 : CycleData E W := ⟨2,![2,14,16,6],![3,4,27,16]⟩
def cycle2545_2 : CycleData E W := ⟨3,![3,20,7,17,10],![4,8,18,16,26]⟩
def cycle2545_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2545_4 : CycleData E W := ⟨3,![15,13,8,21,19],![6,27,14,18,38]⟩
def cycle2545_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2545 : PartitionData E W := ⟨6,![cycle2545_0,cycle2545_1,cycle2545_2,cycle2545_3,cycle2545_4,cycle2545_5]⟩
lemma valid_data2545 : data2545.Valid src2545 dst2545 Finset.univ := by decide +kernel

def src2546 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2546 : E → W := ![6,3,4,8,2,3,16,18,14,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2546_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2546_1 : CycleData E W := ⟨2,![2,14,16,6],![3,4,27,16]⟩
def cycle2546_2 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,26]⟩
def cycle2546_3 : CycleData E W := ⟨4,![4,23,19,15,13,9],![2,8,38,6,27,14]⟩
def cycle2546_4 : CycleData E W := ⟨2,![7,22,18,17],![16,18,38,26]⟩
def cycle2546_5 : CycleData E W := ⟨1,![8,21,12],![14,18,28]⟩
def data2546 : PartitionData E W := ⟨6,![cycle2546_0,cycle2546_1,cycle2546_2,cycle2546_3,cycle2546_4,cycle2546_5]⟩
lemma valid_data2546 : data2546.Valid src2546 dst2546 Finset.univ := by decide +kernel

def src2547 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2547 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2547_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2547_1 : CycleData E W := ⟨2,![2,10,17,6],![3,4,27,16]⟩
def cycle2547_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2547_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,27,14]⟩
def cycle2547_4 : CycleData E W := ⟨2,![8,7,16,12],![14,18,16,26]⟩
def cycle2547_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2547 : PartitionData E W := ⟨6,![cycle2547_0,cycle2547_1,cycle2547_2,cycle2547_3,cycle2547_4,cycle2547_5]⟩
lemma valid_data2547 : data2547.Valid src2547 dst2547 Finset.univ := by decide +kernel

def src2548 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2548 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2548_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2548_1 : CycleData E W := ⟨4,![2,10,11,12,16,6],![3,4,27,14,26,16]⟩
def cycle2548_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2548_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2548_4 : CycleData E W := ⟨2,![7,21,18,17],![16,18,38,27]⟩
def cycle2548_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2548 : PartitionData E W := ⟨6,![cycle2548_0,cycle2548_1,cycle2548_2,cycle2548_3,cycle2548_4,cycle2548_5]⟩
lemma valid_data2548 : data2548.Valid src2548 dst2548 Finset.univ := by decide +kernel

def src2549 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2549 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2549_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2549_1 : CycleData E W := ⟨2,![2,10,17,6],![3,4,27,16]⟩
def cycle2549_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2549_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,27,14]⟩
def cycle2549_4 : CycleData E W := ⟨2,![8,7,16,12],![14,18,16,26]⟩
def cycle2549_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2549 : PartitionData E W := ⟨6,![cycle2549_0,cycle2549_1,cycle2549_2,cycle2549_3,cycle2549_4,cycle2549_5]⟩
lemma valid_data2549 : data2549.Valid src2549 dst2549 Finset.univ := by decide +kernel

def src2550 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2550 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2550_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2550_1 : CycleData E W := ⟨3,![2,14,13,16,6],![3,4,28,26,16]⟩
def cycle2550_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2550_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2550_4 : CycleData E W := ⟨2,![7,21,22,17],![16,18,28,38]⟩
def cycle2550_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2550 : PartitionData E W := ⟨6,![cycle2550_0,cycle2550_1,cycle2550_2,cycle2550_3,cycle2550_4,cycle2550_5]⟩
lemma valid_data2550 : data2550.Valid src2550 dst2550 Finset.univ := by decide +kernel

def src2551 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2551 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2551_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2551_1 : CycleData E W := ⟨4,![2,10,11,12,16,6],![3,4,27,14,26,16]⟩
def cycle2551_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2551_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2551_4 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2551_5 : CycleData E W := ⟨3,![15,13,22,18,19],![6,26,28,38,27]⟩
def data2551 : PartitionData E W := ⟨6,![cycle2551_0,cycle2551_1,cycle2551_2,cycle2551_3,cycle2551_4,cycle2551_5]⟩
lemma valid_data2551 : data2551.Valid src2551 dst2551 Finset.univ := by decide +kernel

def src2552 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2552 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2552_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2552_1 : CycleData E W := ⟨3,![2,14,13,16,6],![3,4,28,26,16]⟩
def cycle2552_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2552_3 : CycleData E W := ⟨3,![4,20,21,8,9],![2,8,28,18,14]⟩
def cycle2552_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2552_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2552 : PartitionData E W := ⟨6,![cycle2552_0,cycle2552_1,cycle2552_2,cycle2552_3,cycle2552_4,cycle2552_5]⟩
lemma valid_data2552 : data2552.Valid src2552 dst2552 Finset.univ := by decide +kernel

def src2553 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2553 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2553_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2553_1 : CycleData E W := ⟨2,![2,10,18,6],![3,4,27,16]⟩
def cycle2553_2 : CycleData E W := ⟨4,![4,3,14,21,8,9],![2,8,4,28,18,14]⟩
def cycle2553_3 : CycleData E W := ⟨2,![20,7,17,23],![8,18,16,38]⟩
def cycle2553_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2553_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2553 : PartitionData E W := ⟨6,![cycle2553_0,cycle2553_1,cycle2553_2,cycle2553_3,cycle2553_4,cycle2553_5]⟩
lemma valid_data2553 : data2553.Valid src2553 dst2553 Finset.univ := by decide +kernel

def src2554 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2554 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2554_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2554_1 : CycleData E W := ⟨2,![2,10,18,6],![3,4,27,16]⟩
def cycle2554_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2554_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,14]⟩
def cycle2554_4 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2554_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2554_6 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2554 : PartitionData E W := ⟨7,![cycle2554_0,cycle2554_1,cycle2554_2,cycle2554_3,cycle2554_4,cycle2554_5,cycle2554_6]⟩
lemma valid_data2554 : data2554.Valid src2554 dst2554 Finset.univ := by decide +kernel

def src2555 : E → W := ![2,6,3,4,8,2,3,16,18,14,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2555 : E → W := ![6,3,4,8,2,3,16,18,14,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2555_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2555_1 : CycleData E W := ⟨2,![2,10,18,6],![3,4,27,16]⟩
def cycle2555_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2555_3 : CycleData E W := ⟨3,![4,23,16,12,9],![2,8,38,26,14]⟩
def cycle2555_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2555_5 : CycleData E W := ⟨4,![15,13,21,8,11,19],![6,26,28,18,14,27]⟩
def data2555 : PartitionData E W := ⟨6,![cycle2555_0,cycle2555_1,cycle2555_2,cycle2555_3,cycle2555_4,cycle2555_5]⟩
lemma valid_data2555 : data2555.Valid src2555 dst2555 Finset.univ := by decide +kernel

def src2556 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2556 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2556_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2556_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2556_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2556_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2556_4 : CycleData E W := ⟨3,![15,16,8,12,19],![6,26,16,14,27]⟩
def cycle2556_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2556 : PartitionData E W := ⟨6,![cycle2556_0,cycle2556_1,cycle2556_2,cycle2556_3,cycle2556_4,cycle2556_5]⟩
lemma valid_data2556 : data2556.Valid src2556 dst2556 Finset.univ := by decide +kernel

def src2557 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2557 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2557_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2557_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2557_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2557_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2557_4 : CycleData E W := ⟨3,![15,16,8,12,19],![6,26,16,14,27]⟩
def cycle2557_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2557 : PartitionData E W := ⟨6,![cycle2557_0,cycle2557_1,cycle2557_2,cycle2557_3,cycle2557_4,cycle2557_5]⟩
lemma valid_data2557 : data2557.Valid src2557 dst2557 Finset.univ := by decide +kernel

def src2558 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2558 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2558_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2558_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2558_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2558_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2558_4 : CycleData E W := ⟨3,![15,16,8,12,19],![6,26,16,14,27]⟩
def cycle2558_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2558 : PartitionData E W := ⟨6,![cycle2558_0,cycle2558_1,cycle2558_2,cycle2558_3,cycle2558_4,cycle2558_5]⟩
lemma valid_data2558 : data2558.Valid src2558 dst2558 Finset.univ := by decide +kernel

def src2559 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2559 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2559_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2559_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2559_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2559_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2559_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle2559_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data2559 : PartitionData E W := ⟨6,![cycle2559_0,cycle2559_1,cycle2559_2,cycle2559_3,cycle2559_4,cycle2559_5]⟩
lemma valid_data2559 : data2559.Valid src2559 dst2559 Finset.univ := by decide +kernel

def src2560 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2560 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2560_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2560_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2560_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2560_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2560_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle2560_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data2560 : PartitionData E W := ⟨6,![cycle2560_0,cycle2560_1,cycle2560_2,cycle2560_3,cycle2560_4,cycle2560_5]⟩
lemma valid_data2560 : data2560.Valid src2560 dst2560 Finset.univ := by decide +kernel

def src2561 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2561 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2561_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2561_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2561_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2561_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2561_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle2561_5 : CycleData E W := ⟨4,![15,16,22,21,13,19],![6,26,38,18,28,27]⟩
def data2561 : PartitionData E W := ⟨6,![cycle2561_0,cycle2561_1,cycle2561_2,cycle2561_3,cycle2561_4,cycle2561_5]⟩
lemma valid_data2561 : data2561.Valid src2561 dst2561 Finset.univ := by decide +kernel

def src2562 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2562 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2562_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2562_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2562_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2562_3 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,26,16]⟩
def cycle2562_4 : CycleData E W := ⟨1,![8,16,12],![14,16,27]⟩
def cycle2562_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2562 : PartitionData E W := ⟨6,![cycle2562_0,cycle2562_1,cycle2562_2,cycle2562_3,cycle2562_4,cycle2562_5]⟩
lemma valid_data2562 : data2562.Valid src2562 dst2562 Finset.univ := by decide +kernel

def src2563 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2563 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2563_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2563_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2563_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2563_3 : CycleData E W := ⟨4,![4,20,21,18,17,9],![2,8,18,38,26,16]⟩
def cycle2563_4 : CycleData E W := ⟨1,![8,16,12],![14,16,27]⟩
def cycle2563_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2563 : PartitionData E W := ⟨6,![cycle2563_0,cycle2563_1,cycle2563_2,cycle2563_3,cycle2563_4,cycle2563_5]⟩
lemma valid_data2563 : data2563.Valid src2563 dst2563 Finset.univ := by decide +kernel

def src2564 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2564 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2564_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2564_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,26,14,18]⟩
def cycle2564_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2564_3 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,26,16]⟩
def cycle2564_4 : CycleData E W := ⟨1,![8,16,12],![14,16,27]⟩
def cycle2564_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2564 : PartitionData E W := ⟨6,![cycle2564_0,cycle2564_1,cycle2564_2,cycle2564_3,cycle2564_4,cycle2564_5]⟩
lemma valid_data2564 : data2564.Valid src2564 dst2564 Finset.univ := by decide +kernel

def src2565 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2565 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2565_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2565_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2565_2 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,27,16]⟩
def cycle2565_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2565_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle2565_5 : CycleData E W := ⟨4,![10,15,19,22,13,14],![4,26,6,38,28,27]⟩
def data2565 : PartitionData E W := ⟨6,![cycle2565_0,cycle2565_1,cycle2565_2,cycle2565_3,cycle2565_4,cycle2565_5]⟩
lemma valid_data2565 : data2565.Valid src2565 dst2565 Finset.univ := by decide +kernel

def src2566 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2566 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2566_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2566_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2566_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle2566_3 : CycleData E W := ⟨3,![15,11,7,21,19],![6,26,14,18,38]⟩
def cycle2566_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2566_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2566 : PartitionData E W := ⟨6,![cycle2566_0,cycle2566_1,cycle2566_2,cycle2566_3,cycle2566_4,cycle2566_5]⟩
lemma valid_data2566 : data2566.Valid src2566 dst2566 Finset.univ := by decide +kernel

def src2567 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2567 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2567_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2567_1 : CycleData E W := ⟨3,![2,14,18,22,6],![3,4,27,38,18]⟩
def cycle2567_2 : CycleData E W := ⟨3,![3,23,19,15,10],![4,8,38,6,26]⟩
def cycle2567_3 : CycleData E W := ⟨3,![4,20,13,17,9],![2,8,28,27,16]⟩
def cycle2567_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2567_5 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def data2567 : PartitionData E W := ⟨6,![cycle2567_0,cycle2567_1,cycle2567_2,cycle2567_3,cycle2567_4,cycle2567_5]⟩
lemma valid_data2567 : data2567.Valid src2567 dst2567 Finset.univ := by decide +kernel

def src2568 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2568 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2568_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2568_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2568_2 : CycleData E W := ⟨4,![4,23,16,11,8,9],![2,8,38,26,14,16]⟩
def cycle2568_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2568_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2568_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2568 : PartitionData E W := ⟨6,![cycle2568_0,cycle2568_1,cycle2568_2,cycle2568_3,cycle2568_4,cycle2568_5]⟩
lemma valid_data2568 : data2568.Valid src2568 dst2568 Finset.univ := by decide +kernel

def src2569 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2569 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2569_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2569_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2569_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle2569_3 : CycleData E W := ⟨2,![7,21,16,11],![14,18,38,26]⟩
def cycle2569_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2569_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2569 : PartitionData E W := ⟨6,![cycle2569_0,cycle2569_1,cycle2569_2,cycle2569_3,cycle2569_4,cycle2569_5]⟩
lemma valid_data2569 : data2569.Valid src2569 dst2569 Finset.univ := by decide +kernel

def src2570 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2570 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2570_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2570_1 : CycleData E W := ⟨3,![2,3,20,21,6],![3,4,8,28,18]⟩
def cycle2570_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2570_3 : CycleData E W := ⟨2,![7,22,16,11],![14,18,38,26]⟩
def cycle2570_4 : CycleData E W := ⟨2,![8,18,13,12],![14,16,27,28]⟩
def cycle2570_5 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def data2570 : PartitionData E W := ⟨6,![cycle2570_0,cycle2570_1,cycle2570_2,cycle2570_3,cycle2570_4,cycle2570_5]⟩
lemma valid_data2570 : data2570.Valid src2570 dst2570 Finset.univ := by decide +kernel

def src2571 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2571 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2571_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2571_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2571_2 : CycleData E W := ⟨4,![4,23,18,11,8,9],![2,8,38,26,14,16]⟩
def cycle2571_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2571_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2571_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2571 : PartitionData E W := ⟨6,![cycle2571_0,cycle2571_1,cycle2571_2,cycle2571_3,cycle2571_4,cycle2571_5]⟩
lemma valid_data2571 : data2571.Valid src2571 dst2571 Finset.univ := by decide +kernel

def src2572 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2572 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2572_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2572_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2572_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle2572_3 : CycleData E W := ⟨2,![7,21,18,11],![14,18,38,26]⟩
def cycle2572_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2572_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2572 : PartitionData E W := ⟨6,![cycle2572_0,cycle2572_1,cycle2572_2,cycle2572_3,cycle2572_4,cycle2572_5]⟩
lemma valid_data2572 : data2572.Valid src2572 dst2572 Finset.univ := by decide +kernel

def src2573 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2573 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2573_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2573_1 : CycleData E W := ⟨3,![2,10,18,22,6],![3,4,26,38,18]⟩
def cycle2573_2 : CycleData E W := ⟨3,![4,3,14,16,9],![2,8,4,27,16]⟩
def cycle2573_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2573_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle2573_5 : CycleData E W := ⟨3,![15,13,20,23,19],![6,27,28,8,38]⟩
def data2573 : PartitionData E W := ⟨6,![cycle2573_0,cycle2573_1,cycle2573_2,cycle2573_3,cycle2573_4,cycle2573_5]⟩
lemma valid_data2573 : data2573.Valid src2573 dst2573 Finset.univ := by decide +kernel

def src2574 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2574 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2574_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2574_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2574_2 : CycleData E W := ⟨4,![4,23,18,13,8,9],![2,8,38,27,14,16]⟩
def cycle2574_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2574_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2574_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2574 : PartitionData E W := ⟨6,![cycle2574_0,cycle2574_1,cycle2574_2,cycle2574_3,cycle2574_4,cycle2574_5]⟩
lemma valid_data2574 : data2574.Valid src2574 dst2574 Finset.univ := by decide +kernel

def src2575 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2575 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2575_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2575_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2575_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle2575_3 : CycleData E W := ⟨2,![7,21,18,13],![14,18,38,27]⟩
def cycle2575_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2575_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2575 : PartitionData E W := ⟨6,![cycle2575_0,cycle2575_1,cycle2575_2,cycle2575_3,cycle2575_4,cycle2575_5]⟩
lemma valid_data2575 : data2575.Valid src2575 dst2575 Finset.univ := by decide +kernel

def src2576 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2576 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2576_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2576_1 : CycleData E W := ⟨3,![2,14,18,22,6],![3,4,27,38,18]⟩
def cycle2576_2 : CycleData E W := ⟨3,![4,3,10,16,9],![2,8,4,26,16]⟩
def cycle2576_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2576_4 : CycleData E W := ⟨1,![8,17,13],![14,16,27]⟩
def cycle2576_5 : CycleData E W := ⟨3,![15,11,20,23,19],![6,26,28,8,38]⟩
def data2576 : PartitionData E W := ⟨6,![cycle2576_0,cycle2576_1,cycle2576_2,cycle2576_3,cycle2576_4,cycle2576_5]⟩
lemma valid_data2576 : data2576.Valid src2576 dst2576 Finset.univ := by decide +kernel

def src2577 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2577 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2577_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2577_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2577_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2577_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2577_4 : CycleData E W := ⟨3,![10,16,8,13,14],![4,26,16,14,27]⟩
def cycle2577_5 : CycleData E W := ⟨3,![15,11,22,18,19],![6,26,28,38,27]⟩
def data2577 : PartitionData E W := ⟨6,![cycle2577_0,cycle2577_1,cycle2577_2,cycle2577_3,cycle2577_4,cycle2577_5]⟩
lemma valid_data2577 : data2577.Valid src2577 dst2577 Finset.univ := by decide +kernel

def src2578 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2578 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2578_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2578_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2578_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle2578_3 : CycleData E W := ⟨2,![7,21,18,13],![14,18,38,27]⟩
def cycle2578_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2578_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data2578 : PartitionData E W := ⟨6,![cycle2578_0,cycle2578_1,cycle2578_2,cycle2578_3,cycle2578_4,cycle2578_5]⟩
lemma valid_data2578 : data2578.Valid src2578 dst2578 Finset.univ := by decide +kernel

def src2579 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2579 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2579_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2579_1 : CycleData E W := ⟨3,![2,3,20,21,6],![3,4,8,28,18]⟩
def cycle2579_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2579_3 : CycleData E W := ⟨2,![7,22,18,13],![14,18,38,27]⟩
def cycle2579_4 : CycleData E W := ⟨2,![8,16,11,12],![14,16,26,28]⟩
def cycle2579_5 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def data2579 : PartitionData E W := ⟨6,![cycle2579_0,cycle2579_1,cycle2579_2,cycle2579_3,cycle2579_4,cycle2579_5]⟩
lemma valid_data2579 : data2579.Valid src2579 dst2579 Finset.univ := by decide +kernel

def src2580 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2580 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2580_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2580_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2580_2 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,26,16]⟩
def cycle2580_3 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2580_4 : CycleData E W := ⟨1,![8,16,13],![14,16,27]⟩
def cycle2580_5 : CycleData E W := ⟨4,![10,11,22,19,15,14],![4,26,28,38,6,27]⟩
def data2580 : PartitionData E W := ⟨6,![cycle2580_0,cycle2580_1,cycle2580_2,cycle2580_3,cycle2580_4,cycle2580_5]⟩
lemma valid_data2580 : data2580.Valid src2580 dst2580 Finset.univ := by decide +kernel

def src2581 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2581 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2581_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2581_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2581_2 : CycleData E W := ⟨3,![4,23,12,8,9],![2,8,28,14,16]⟩
def cycle2581_3 : CycleData E W := ⟨3,![15,13,7,21,19],![6,27,14,18,38]⟩
def cycle2581_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2581_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2581 : PartitionData E W := ⟨6,![cycle2581_0,cycle2581_1,cycle2581_2,cycle2581_3,cycle2581_4,cycle2581_5]⟩
lemma valid_data2581 : data2581.Valid src2581 dst2581 Finset.univ := by decide +kernel

def src2582 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2582 : E → W := ![6,3,4,8,2,3,18,14,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2582_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2582_1 : CycleData E W := ⟨3,![2,10,18,22,6],![3,4,26,38,18]⟩
def cycle2582_2 : CycleData E W := ⟨3,![3,23,19,15,14],![4,8,38,6,27]⟩
def cycle2582_3 : CycleData E W := ⟨3,![4,20,11,17,9],![2,8,28,26,16]⟩
def cycle2582_4 : CycleData E W := ⟨1,![7,21,12],![14,18,28]⟩
def cycle2582_5 : CycleData E W := ⟨1,![8,16,13],![14,16,27]⟩
def data2582 : PartitionData E W := ⟨6,![cycle2582_0,cycle2582_1,cycle2582_2,cycle2582_3,cycle2582_4,cycle2582_5]⟩
lemma valid_data2582 : data2582.Valid src2582 dst2582 Finset.univ := by decide +kernel

def src2583 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2583 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2583_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2583_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2583_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2583_3 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,27,16]⟩
def cycle2583_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2583_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2583 : PartitionData E W := ⟨6,![cycle2583_0,cycle2583_1,cycle2583_2,cycle2583_3,cycle2583_4,cycle2583_5]⟩
lemma valid_data2583 : data2583.Valid src2583 dst2583 Finset.univ := by decide +kernel

def src2584 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2584 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2584_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2584_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2584_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2584_3 : CycleData E W := ⟨4,![4,20,21,18,17,9],![2,8,18,38,27,16]⟩
def cycle2584_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2584_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2584 : PartitionData E W := ⟨6,![cycle2584_0,cycle2584_1,cycle2584_2,cycle2584_3,cycle2584_4,cycle2584_5]⟩
lemma valid_data2584 : data2584.Valid src2584 dst2584 Finset.univ := by decide +kernel

def src2585 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2585 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2585_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2585_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2585_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2585_3 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,27,16]⟩
def cycle2585_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2585_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2585 : PartitionData E W := ⟨6,![cycle2585_0,cycle2585_1,cycle2585_2,cycle2585_3,cycle2585_4,cycle2585_5]⟩
lemma valid_data2585 : data2585.Valid src2585 dst2585 Finset.univ := by decide +kernel

def src2586 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2586 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2586_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2586_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2586_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2586_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2586_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2586_5 : CycleData E W := ⟨3,![15,13,22,18,19],![6,26,28,38,27]⟩
def data2586 : PartitionData E W := ⟨6,![cycle2586_0,cycle2586_1,cycle2586_2,cycle2586_3,cycle2586_4,cycle2586_5]⟩
lemma valid_data2586 : data2586.Valid src2586 dst2586 Finset.univ := by decide +kernel

def src2587 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2587 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2587_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2587_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2587_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2587_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2587_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2587_5 : CycleData E W := ⟨3,![15,13,22,18,19],![6,26,28,38,27]⟩
def data2587 : PartitionData E W := ⟨6,![cycle2587_0,cycle2587_1,cycle2587_2,cycle2587_3,cycle2587_4,cycle2587_5]⟩
lemma valid_data2587 : data2587.Valid src2587 dst2587 Finset.univ := by decide +kernel

def src2588 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2588 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2588_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2588_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2588_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2588_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2588_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2588_5 : CycleData E W := ⟨4,![15,13,21,22,18,19],![6,26,28,18,38,27]⟩
def data2588 : PartitionData E W := ⟨6,![cycle2588_0,cycle2588_1,cycle2588_2,cycle2588_3,cycle2588_4,cycle2588_5]⟩
lemma valid_data2588 : data2588.Valid src2588 dst2588 Finset.univ := by decide +kernel

def src2589 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2589 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2589_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2589_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2589_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2589_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2589_4 : CycleData E W := ⟨3,![15,12,8,18,19],![6,26,14,16,27]⟩
def cycle2589_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2589 : PartitionData E W := ⟨6,![cycle2589_0,cycle2589_1,cycle2589_2,cycle2589_3,cycle2589_4,cycle2589_5]⟩
lemma valid_data2589 : data2589.Valid src2589 dst2589 Finset.univ := by decide +kernel

def src2590 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2590 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2590_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2590_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2590_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2590_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2590_4 : CycleData E W := ⟨3,![15,12,8,18,19],![6,26,14,16,27]⟩
def cycle2590_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2590 : PartitionData E W := ⟨6,![cycle2590_0,cycle2590_1,cycle2590_2,cycle2590_3,cycle2590_4,cycle2590_5]⟩
lemma valid_data2590 : data2590.Valid src2590 dst2590 Finset.univ := by decide +kernel

def src2591 : E → W := ![2,6,3,4,8,2,3,18,14,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2591 : E → W := ![6,3,4,8,2,3,18,14,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2591_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2591_1 : CycleData E W := ⟨3,![2,10,11,7,6],![3,4,27,14,18]⟩
def cycle2591_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2591_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2591_4 : CycleData E W := ⟨3,![15,12,8,18,19],![6,26,14,16,27]⟩
def cycle2591_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2591 : PartitionData E W := ⟨6,![cycle2591_0,cycle2591_1,cycle2591_2,cycle2591_3,cycle2591_4,cycle2591_5]⟩
lemma valid_data2591 : data2591.Valid src2591 dst2591 Finset.univ := by decide +kernel

def src2592 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2592 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2592_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2592_1 : CycleData E W := ⟨3,![2,10,16,7,6],![3,4,26,16,18]⟩
def cycle2592_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2592_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle2592_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2592_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2592 : PartitionData E W := ⟨6,![cycle2592_0,cycle2592_1,cycle2592_2,cycle2592_3,cycle2592_4,cycle2592_5]⟩
lemma valid_data2592 : data2592.Valid src2592 dst2592 Finset.univ := by decide +kernel

def src2593 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2593 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2593_0 : CycleData E W := ⟨2,![0,19,12,9],![2,6,27,14]⟩
def cycle2593_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle2593_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2593_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,3]⟩
def cycle2593_4 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2593_5 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle2593_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2593 : PartitionData E W := ⟨7,![cycle2593_0,cycle2593_1,cycle2593_2,cycle2593_3,cycle2593_4,cycle2593_5,cycle2593_6]⟩
lemma valid_data2593 : data2593.Valid src2593 dst2593 Finset.univ := by decide +kernel

def src2594 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2594 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2594_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2594_1 : CycleData E W := ⟨3,![2,10,16,7,6],![3,4,26,16,18]⟩
def cycle2594_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2594_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle2594_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2594_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2594 : PartitionData E W := ⟨6,![cycle2594_0,cycle2594_1,cycle2594_2,cycle2594_3,cycle2594_4,cycle2594_5]⟩
lemma valid_data2594 : data2594.Valid src2594 dst2594 Finset.univ := by decide +kernel

def src2595 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2595 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2595_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2595_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2595_2 : CycleData E W := ⟨3,![4,23,16,11,9],![2,8,38,26,14]⟩
def cycle2595_3 : CycleData E W := ⟨2,![7,21,22,17],![16,18,28,38]⟩
def cycle2595_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle2595_5 : CycleData E W := ⟨3,![10,15,19,13,14],![4,26,6,27,28]⟩
def data2595 : PartitionData E W := ⟨6,![cycle2595_0,cycle2595_1,cycle2595_2,cycle2595_3,cycle2595_4,cycle2595_5]⟩
lemma valid_data2595 : data2595.Valid src2595 dst2595 Finset.univ := by decide +kernel

def src2596 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2596 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2596_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2596_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2596_2 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,27,14]⟩
def cycle2596_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2596_4 : CycleData E W := ⟨3,![15,11,8,18,19],![6,26,14,16,27]⟩
def cycle2596_5 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def data2596 : PartitionData E W := ⟨6,![cycle2596_0,cycle2596_1,cycle2596_2,cycle2596_3,cycle2596_4,cycle2596_5]⟩
lemma valid_data2596 : data2596.Valid src2596 dst2596 Finset.univ := by decide +kernel

def src2597 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2597 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2597_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2597_1 : CycleData E W := ⟨2,![2,14,21,6],![3,4,28,18]⟩
def cycle2597_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,26,14]⟩
def cycle2597_3 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2597_4 : CycleData E W := ⟨1,![8,18,12],![14,16,27]⟩
def cycle2597_5 : CycleData E W := ⟨4,![15,16,23,20,13,19],![6,26,38,8,28,27]⟩
def data2597 : PartitionData E W := ⟨6,![cycle2597_0,cycle2597_1,cycle2597_2,cycle2597_3,cycle2597_4,cycle2597_5]⟩
lemma valid_data2597 : data2597.Valid src2597 dst2597 Finset.univ := by decide +kernel

def src2598 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2598 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2598_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2598_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,26,16,18]⟩
def cycle2598_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2598_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,26,14]⟩
def cycle2598_4 : CycleData E W := ⟨1,![8,16,12],![14,16,27]⟩
def cycle2598_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2598 : PartitionData E W := ⟨6,![cycle2598_0,cycle2598_1,cycle2598_2,cycle2598_3,cycle2598_4,cycle2598_5]⟩
lemma valid_data2598 : data2598.Valid src2598 dst2598 Finset.univ := by decide +kernel

def src2599 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2599 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2599_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2599_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,26,16,18]⟩
def cycle2599_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2599_3 : CycleData E W := ⟨4,![4,20,21,18,11,9],![2,8,18,38,26,14]⟩
def cycle2599_4 : CycleData E W := ⟨1,![8,16,12],![14,16,27]⟩
def cycle2599_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2599 : PartitionData E W := ⟨6,![cycle2599_0,cycle2599_1,cycle2599_2,cycle2599_3,cycle2599_4,cycle2599_5]⟩
lemma valid_data2599 : data2599.Valid src2599 dst2599 Finset.univ := by decide +kernel

def lookupB12 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data2400 else (if j < 2 then data2401 else data2402)) else (if j < 4 then data2403 else (if j < 5 then data2404 else data2405))) else (if j < 9 then (if j < 7 then data2406 else (if j < 8 then data2407 else data2408)) else (if j < 10 then data2409 else (if j < 11 then data2410 else data2411)))) else (if j < 18 then (if j < 15 then (if j < 13 then data2412 else (if j < 14 then data2413 else data2414)) else (if j < 16 then data2415 else (if j < 17 then data2416 else data2417))) else (if j < 21 then (if j < 19 then data2418 else (if j < 20 then data2419 else data2420)) else (if j < 23 then (if j < 22 then data2421 else data2422) else (if j < 24 then data2423 else data2424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data2425 else (if j < 27 then data2426 else data2427)) else (if j < 29 then data2428 else (if j < 30 then data2429 else data2430))) else (if j < 34 then (if j < 32 then data2431 else (if j < 33 then data2432 else data2433)) else (if j < 35 then data2434 else (if j < 36 then data2435 else data2436)))) else (if j < 43 then (if j < 40 then (if j < 38 then data2437 else (if j < 39 then data2438 else data2439)) else (if j < 41 then data2440 else (if j < 42 then data2441 else data2442))) else (if j < 46 then (if j < 44 then data2443 else (if j < 45 then data2444 else data2445)) else (if j < 48 then (if j < 47 then data2446 else data2447) else (if j < 49 then data2448 else data2449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data2450 else (if j < 52 then data2451 else data2452)) else (if j < 54 then data2453 else (if j < 55 then data2454 else data2455))) else (if j < 59 then (if j < 57 then data2456 else (if j < 58 then data2457 else data2458)) else (if j < 60 then data2459 else (if j < 61 then data2460 else data2461)))) else (if j < 68 then (if j < 65 then (if j < 63 then data2462 else (if j < 64 then data2463 else data2464)) else (if j < 66 then data2465 else (if j < 67 then data2466 else data2467))) else (if j < 71 then (if j < 69 then data2468 else (if j < 70 then data2469 else data2470)) else (if j < 73 then (if j < 72 then data2471 else data2472) else (if j < 74 then data2473 else data2474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data2475 else (if j < 77 then data2476 else data2477)) else (if j < 79 then data2478 else (if j < 80 then data2479 else data2480))) else (if j < 84 then (if j < 82 then data2481 else (if j < 83 then data2482 else data2483)) else (if j < 85 then data2484 else (if j < 86 then data2485 else data2486)))) else (if j < 93 then (if j < 90 then (if j < 88 then data2487 else (if j < 89 then data2488 else data2489)) else (if j < 91 then data2490 else (if j < 92 then data2491 else data2492))) else (if j < 96 then (if j < 94 then data2493 else (if j < 95 then data2494 else data2495)) else (if j < 98 then (if j < 97 then data2496 else data2497) else (if j < 99 then data2498 else data2499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data2500 else (if j < 102 then data2501 else data2502)) else (if j < 104 then data2503 else (if j < 105 then data2504 else data2505))) else (if j < 109 then (if j < 107 then data2506 else (if j < 108 then data2507 else data2508)) else (if j < 110 then data2509 else (if j < 111 then data2510 else data2511)))) else (if j < 118 then (if j < 115 then (if j < 113 then data2512 else (if j < 114 then data2513 else data2514)) else (if j < 116 then data2515 else (if j < 117 then data2516 else data2517))) else (if j < 121 then (if j < 119 then data2518 else (if j < 120 then data2519 else data2520)) else (if j < 123 then (if j < 122 then data2521 else data2522) else (if j < 124 then data2523 else data2524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data2525 else (if j < 127 then data2526 else data2527)) else (if j < 129 then data2528 else (if j < 130 then data2529 else data2530))) else (if j < 134 then (if j < 132 then data2531 else (if j < 133 then data2532 else data2533)) else (if j < 135 then data2534 else (if j < 136 then data2535 else data2536)))) else (if j < 143 then (if j < 140 then (if j < 138 then data2537 else (if j < 139 then data2538 else data2539)) else (if j < 141 then data2540 else (if j < 142 then data2541 else data2542))) else (if j < 146 then (if j < 144 then data2543 else (if j < 145 then data2544 else data2545)) else (if j < 148 then (if j < 147 then data2546 else data2547) else (if j < 149 then data2548 else data2549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data2550 else (if j < 152 then data2551 else data2552)) else (if j < 154 then data2553 else (if j < 155 then data2554 else data2555))) else (if j < 159 then (if j < 157 then data2556 else (if j < 158 then data2557 else data2558)) else (if j < 160 then data2559 else (if j < 161 then data2560 else data2561)))) else (if j < 168 then (if j < 165 then (if j < 163 then data2562 else (if j < 164 then data2563 else data2564)) else (if j < 166 then data2565 else (if j < 167 then data2566 else data2567))) else (if j < 171 then (if j < 169 then data2568 else (if j < 170 then data2569 else data2570)) else (if j < 173 then (if j < 172 then data2571 else data2572) else (if j < 174 then data2573 else data2574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data2575 else (if j < 177 then data2576 else data2577)) else (if j < 179 then data2578 else (if j < 180 then data2579 else data2580))) else (if j < 184 then (if j < 182 then data2581 else (if j < 183 then data2582 else data2583)) else (if j < 185 then data2584 else (if j < 186 then data2585 else data2586)))) else (if j < 193 then (if j < 190 then (if j < 188 then data2587 else (if j < 189 then data2588 else data2589)) else (if j < 191 then data2590 else (if j < 192 then data2591 else data2592))) else (if j < 196 then (if j < 194 then data2593 else (if j < 195 then data2594 else data2595)) else (if j < 198 then (if j < 197 then data2596 else data2597) else (if j < 199 then data2598 else data2599))))))))

def srcTableB12 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src2400 else (if j < 2 then src2401 else src2402)) else (if j < 4 then src2403 else (if j < 5 then src2404 else src2405))) else (if j < 9 then (if j < 7 then src2406 else (if j < 8 then src2407 else src2408)) else (if j < 10 then src2409 else (if j < 11 then src2410 else src2411)))) else (if j < 18 then (if j < 15 then (if j < 13 then src2412 else (if j < 14 then src2413 else src2414)) else (if j < 16 then src2415 else (if j < 17 then src2416 else src2417))) else (if j < 21 then (if j < 19 then src2418 else (if j < 20 then src2419 else src2420)) else (if j < 23 then (if j < 22 then src2421 else src2422) else (if j < 24 then src2423 else src2424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src2425 else (if j < 27 then src2426 else src2427)) else (if j < 29 then src2428 else (if j < 30 then src2429 else src2430))) else (if j < 34 then (if j < 32 then src2431 else (if j < 33 then src2432 else src2433)) else (if j < 35 then src2434 else (if j < 36 then src2435 else src2436)))) else (if j < 43 then (if j < 40 then (if j < 38 then src2437 else (if j < 39 then src2438 else src2439)) else (if j < 41 then src2440 else (if j < 42 then src2441 else src2442))) else (if j < 46 then (if j < 44 then src2443 else (if j < 45 then src2444 else src2445)) else (if j < 48 then (if j < 47 then src2446 else src2447) else (if j < 49 then src2448 else src2449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src2450 else (if j < 52 then src2451 else src2452)) else (if j < 54 then src2453 else (if j < 55 then src2454 else src2455))) else (if j < 59 then (if j < 57 then src2456 else (if j < 58 then src2457 else src2458)) else (if j < 60 then src2459 else (if j < 61 then src2460 else src2461)))) else (if j < 68 then (if j < 65 then (if j < 63 then src2462 else (if j < 64 then src2463 else src2464)) else (if j < 66 then src2465 else (if j < 67 then src2466 else src2467))) else (if j < 71 then (if j < 69 then src2468 else (if j < 70 then src2469 else src2470)) else (if j < 73 then (if j < 72 then src2471 else src2472) else (if j < 74 then src2473 else src2474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src2475 else (if j < 77 then src2476 else src2477)) else (if j < 79 then src2478 else (if j < 80 then src2479 else src2480))) else (if j < 84 then (if j < 82 then src2481 else (if j < 83 then src2482 else src2483)) else (if j < 85 then src2484 else (if j < 86 then src2485 else src2486)))) else (if j < 93 then (if j < 90 then (if j < 88 then src2487 else (if j < 89 then src2488 else src2489)) else (if j < 91 then src2490 else (if j < 92 then src2491 else src2492))) else (if j < 96 then (if j < 94 then src2493 else (if j < 95 then src2494 else src2495)) else (if j < 98 then (if j < 97 then src2496 else src2497) else (if j < 99 then src2498 else src2499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src2500 else (if j < 102 then src2501 else src2502)) else (if j < 104 then src2503 else (if j < 105 then src2504 else src2505))) else (if j < 109 then (if j < 107 then src2506 else (if j < 108 then src2507 else src2508)) else (if j < 110 then src2509 else (if j < 111 then src2510 else src2511)))) else (if j < 118 then (if j < 115 then (if j < 113 then src2512 else (if j < 114 then src2513 else src2514)) else (if j < 116 then src2515 else (if j < 117 then src2516 else src2517))) else (if j < 121 then (if j < 119 then src2518 else (if j < 120 then src2519 else src2520)) else (if j < 123 then (if j < 122 then src2521 else src2522) else (if j < 124 then src2523 else src2524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src2525 else (if j < 127 then src2526 else src2527)) else (if j < 129 then src2528 else (if j < 130 then src2529 else src2530))) else (if j < 134 then (if j < 132 then src2531 else (if j < 133 then src2532 else src2533)) else (if j < 135 then src2534 else (if j < 136 then src2535 else src2536)))) else (if j < 143 then (if j < 140 then (if j < 138 then src2537 else (if j < 139 then src2538 else src2539)) else (if j < 141 then src2540 else (if j < 142 then src2541 else src2542))) else (if j < 146 then (if j < 144 then src2543 else (if j < 145 then src2544 else src2545)) else (if j < 148 then (if j < 147 then src2546 else src2547) else (if j < 149 then src2548 else src2549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src2550 else (if j < 152 then src2551 else src2552)) else (if j < 154 then src2553 else (if j < 155 then src2554 else src2555))) else (if j < 159 then (if j < 157 then src2556 else (if j < 158 then src2557 else src2558)) else (if j < 160 then src2559 else (if j < 161 then src2560 else src2561)))) else (if j < 168 then (if j < 165 then (if j < 163 then src2562 else (if j < 164 then src2563 else src2564)) else (if j < 166 then src2565 else (if j < 167 then src2566 else src2567))) else (if j < 171 then (if j < 169 then src2568 else (if j < 170 then src2569 else src2570)) else (if j < 173 then (if j < 172 then src2571 else src2572) else (if j < 174 then src2573 else src2574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src2575 else (if j < 177 then src2576 else src2577)) else (if j < 179 then src2578 else (if j < 180 then src2579 else src2580))) else (if j < 184 then (if j < 182 then src2581 else (if j < 183 then src2582 else src2583)) else (if j < 185 then src2584 else (if j < 186 then src2585 else src2586)))) else (if j < 193 then (if j < 190 then (if j < 188 then src2587 else (if j < 189 then src2588 else src2589)) else (if j < 191 then src2590 else (if j < 192 then src2591 else src2592))) else (if j < 196 then (if j < 194 then src2593 else (if j < 195 then src2594 else src2595)) else (if j < 198 then (if j < 197 then src2596 else src2597) else (if j < 199 then src2598 else src2599))))))))

def dstTableB12 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst2400 else (if j < 2 then dst2401 else dst2402)) else (if j < 4 then dst2403 else (if j < 5 then dst2404 else dst2405))) else (if j < 9 then (if j < 7 then dst2406 else (if j < 8 then dst2407 else dst2408)) else (if j < 10 then dst2409 else (if j < 11 then dst2410 else dst2411)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst2412 else (if j < 14 then dst2413 else dst2414)) else (if j < 16 then dst2415 else (if j < 17 then dst2416 else dst2417))) else (if j < 21 then (if j < 19 then dst2418 else (if j < 20 then dst2419 else dst2420)) else (if j < 23 then (if j < 22 then dst2421 else dst2422) else (if j < 24 then dst2423 else dst2424))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst2425 else (if j < 27 then dst2426 else dst2427)) else (if j < 29 then dst2428 else (if j < 30 then dst2429 else dst2430))) else (if j < 34 then (if j < 32 then dst2431 else (if j < 33 then dst2432 else dst2433)) else (if j < 35 then dst2434 else (if j < 36 then dst2435 else dst2436)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst2437 else (if j < 39 then dst2438 else dst2439)) else (if j < 41 then dst2440 else (if j < 42 then dst2441 else dst2442))) else (if j < 46 then (if j < 44 then dst2443 else (if j < 45 then dst2444 else dst2445)) else (if j < 48 then (if j < 47 then dst2446 else dst2447) else (if j < 49 then dst2448 else dst2449)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst2450 else (if j < 52 then dst2451 else dst2452)) else (if j < 54 then dst2453 else (if j < 55 then dst2454 else dst2455))) else (if j < 59 then (if j < 57 then dst2456 else (if j < 58 then dst2457 else dst2458)) else (if j < 60 then dst2459 else (if j < 61 then dst2460 else dst2461)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst2462 else (if j < 64 then dst2463 else dst2464)) else (if j < 66 then dst2465 else (if j < 67 then dst2466 else dst2467))) else (if j < 71 then (if j < 69 then dst2468 else (if j < 70 then dst2469 else dst2470)) else (if j < 73 then (if j < 72 then dst2471 else dst2472) else (if j < 74 then dst2473 else dst2474))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst2475 else (if j < 77 then dst2476 else dst2477)) else (if j < 79 then dst2478 else (if j < 80 then dst2479 else dst2480))) else (if j < 84 then (if j < 82 then dst2481 else (if j < 83 then dst2482 else dst2483)) else (if j < 85 then dst2484 else (if j < 86 then dst2485 else dst2486)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst2487 else (if j < 89 then dst2488 else dst2489)) else (if j < 91 then dst2490 else (if j < 92 then dst2491 else dst2492))) else (if j < 96 then (if j < 94 then dst2493 else (if j < 95 then dst2494 else dst2495)) else (if j < 98 then (if j < 97 then dst2496 else dst2497) else (if j < 99 then dst2498 else dst2499))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst2500 else (if j < 102 then dst2501 else dst2502)) else (if j < 104 then dst2503 else (if j < 105 then dst2504 else dst2505))) else (if j < 109 then (if j < 107 then dst2506 else (if j < 108 then dst2507 else dst2508)) else (if j < 110 then dst2509 else (if j < 111 then dst2510 else dst2511)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst2512 else (if j < 114 then dst2513 else dst2514)) else (if j < 116 then dst2515 else (if j < 117 then dst2516 else dst2517))) else (if j < 121 then (if j < 119 then dst2518 else (if j < 120 then dst2519 else dst2520)) else (if j < 123 then (if j < 122 then dst2521 else dst2522) else (if j < 124 then dst2523 else dst2524))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst2525 else (if j < 127 then dst2526 else dst2527)) else (if j < 129 then dst2528 else (if j < 130 then dst2529 else dst2530))) else (if j < 134 then (if j < 132 then dst2531 else (if j < 133 then dst2532 else dst2533)) else (if j < 135 then dst2534 else (if j < 136 then dst2535 else dst2536)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst2537 else (if j < 139 then dst2538 else dst2539)) else (if j < 141 then dst2540 else (if j < 142 then dst2541 else dst2542))) else (if j < 146 then (if j < 144 then dst2543 else (if j < 145 then dst2544 else dst2545)) else (if j < 148 then (if j < 147 then dst2546 else dst2547) else (if j < 149 then dst2548 else dst2549)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst2550 else (if j < 152 then dst2551 else dst2552)) else (if j < 154 then dst2553 else (if j < 155 then dst2554 else dst2555))) else (if j < 159 then (if j < 157 then dst2556 else (if j < 158 then dst2557 else dst2558)) else (if j < 160 then dst2559 else (if j < 161 then dst2560 else dst2561)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst2562 else (if j < 164 then dst2563 else dst2564)) else (if j < 166 then dst2565 else (if j < 167 then dst2566 else dst2567))) else (if j < 171 then (if j < 169 then dst2568 else (if j < 170 then dst2569 else dst2570)) else (if j < 173 then (if j < 172 then dst2571 else dst2572) else (if j < 174 then dst2573 else dst2574))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst2575 else (if j < 177 then dst2576 else dst2577)) else (if j < 179 then dst2578 else (if j < 180 then dst2579 else dst2580))) else (if j < 184 then (if j < 182 then dst2581 else (if j < 183 then dst2582 else dst2583)) else (if j < 185 then dst2584 else (if j < 186 then dst2585 else dst2586)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst2587 else (if j < 189 then dst2588 else dst2589)) else (if j < 191 then dst2590 else (if j < 192 then dst2591 else dst2592))) else (if j < 196 then (if j < 194 then dst2593 else (if j < 195 then dst2594 else dst2595)) else (if j < 198 then (if j < 197 then dst2596 else dst2597) else (if j < 199 then dst2598 else dst2599))))))))

def caseB12 (i : Fin 200) : Cases := ⟨2400 + i.val,by have := i.isLt; omega⟩
lemma tableB12_valid (i : Fin 200) :
    (lookupB12 i.val).Valid (srcTableB12 i.val) (dstTableB12 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data2400
  · exact valid_data2401
  · exact valid_data2402
  · exact valid_data2403
  · exact valid_data2404
  · exact valid_data2405
  · exact valid_data2406
  · exact valid_data2407
  · exact valid_data2408
  · exact valid_data2409
  · exact valid_data2410
  · exact valid_data2411
  · exact valid_data2412
  · exact valid_data2413
  · exact valid_data2414
  · exact valid_data2415
  · exact valid_data2416
  · exact valid_data2417
  · exact valid_data2418
  · exact valid_data2419
  · exact valid_data2420
  · exact valid_data2421
  · exact valid_data2422
  · exact valid_data2423
  · exact valid_data2424
  · exact valid_data2425
  · exact valid_data2426
  · exact valid_data2427
  · exact valid_data2428
  · exact valid_data2429
  · exact valid_data2430
  · exact valid_data2431
  · exact valid_data2432
  · exact valid_data2433
  · exact valid_data2434
  · exact valid_data2435
  · exact valid_data2436
  · exact valid_data2437
  · exact valid_data2438
  · exact valid_data2439
  · exact valid_data2440
  · exact valid_data2441
  · exact valid_data2442
  · exact valid_data2443
  · exact valid_data2444
  · exact valid_data2445
  · exact valid_data2446
  · exact valid_data2447
  · exact valid_data2448
  · exact valid_data2449
  · exact valid_data2450
  · exact valid_data2451
  · exact valid_data2452
  · exact valid_data2453
  · exact valid_data2454
  · exact valid_data2455
  · exact valid_data2456
  · exact valid_data2457
  · exact valid_data2458
  · exact valid_data2459
  · exact valid_data2460
  · exact valid_data2461
  · exact valid_data2462
  · exact valid_data2463
  · exact valid_data2464
  · exact valid_data2465
  · exact valid_data2466
  · exact valid_data2467
  · exact valid_data2468
  · exact valid_data2469
  · exact valid_data2470
  · exact valid_data2471
  · exact valid_data2472
  · exact valid_data2473
  · exact valid_data2474
  · exact valid_data2475
  · exact valid_data2476
  · exact valid_data2477
  · exact valid_data2478
  · exact valid_data2479
  · exact valid_data2480
  · exact valid_data2481
  · exact valid_data2482
  · exact valid_data2483
  · exact valid_data2484
  · exact valid_data2485
  · exact valid_data2486
  · exact valid_data2487
  · exact valid_data2488
  · exact valid_data2489
  · exact valid_data2490
  · exact valid_data2491
  · exact valid_data2492
  · exact valid_data2493
  · exact valid_data2494
  · exact valid_data2495
  · exact valid_data2496
  · exact valid_data2497
  · exact valid_data2498
  · exact valid_data2499
  · exact valid_data2500
  · exact valid_data2501
  · exact valid_data2502
  · exact valid_data2503
  · exact valid_data2504
  · exact valid_data2505
  · exact valid_data2506
  · exact valid_data2507
  · exact valid_data2508
  · exact valid_data2509
  · exact valid_data2510
  · exact valid_data2511
  · exact valid_data2512
  · exact valid_data2513
  · exact valid_data2514
  · exact valid_data2515
  · exact valid_data2516
  · exact valid_data2517
  · exact valid_data2518
  · exact valid_data2519
  · exact valid_data2520
  · exact valid_data2521
  · exact valid_data2522
  · exact valid_data2523
  · exact valid_data2524
  · exact valid_data2525
  · exact valid_data2526
  · exact valid_data2527
  · exact valid_data2528
  · exact valid_data2529
  · exact valid_data2530
  · exact valid_data2531
  · exact valid_data2532
  · exact valid_data2533
  · exact valid_data2534
  · exact valid_data2535
  · exact valid_data2536
  · exact valid_data2537
  · exact valid_data2538
  · exact valid_data2539
  · exact valid_data2540
  · exact valid_data2541
  · exact valid_data2542
  · exact valid_data2543
  · exact valid_data2544
  · exact valid_data2545
  · exact valid_data2546
  · exact valid_data2547
  · exact valid_data2548
  · exact valid_data2549
  · exact valid_data2550
  · exact valid_data2551
  · exact valid_data2552
  · exact valid_data2553
  · exact valid_data2554
  · exact valid_data2555
  · exact valid_data2556
  · exact valid_data2557
  · exact valid_data2558
  · exact valid_data2559
  · exact valid_data2560
  · exact valid_data2561
  · exact valid_data2562
  · exact valid_data2563
  · exact valid_data2564
  · exact valid_data2565
  · exact valid_data2566
  · exact valid_data2567
  · exact valid_data2568
  · exact valid_data2569
  · exact valid_data2570
  · exact valid_data2571
  · exact valid_data2572
  · exact valid_data2573
  · exact valid_data2574
  · exact valid_data2575
  · exact valid_data2576
  · exact valid_data2577
  · exact valid_data2578
  · exact valid_data2579
  · exact valid_data2580
  · exact valid_data2581
  · exact valid_data2582
  · exact valid_data2583
  · exact valid_data2584
  · exact valid_data2585
  · exact valid_data2586
  · exact valid_data2587
  · exact valid_data2588
  · exact valid_data2589
  · exact valid_data2590
  · exact valid_data2591
  · exact valid_data2592
  · exact valid_data2593
  · exact valid_data2594
  · exact valid_data2595
  · exact valid_data2596
  · exact valid_data2597
  · exact valid_data2598
  · exact valid_data2599

lemma srcB12_row : ∀ (i : Fin 200) (e : E),
    srcTableB12 i.val e = caseSource (caseB12 i) e := by decide +kernel

lemma dstB12_row : ∀ (i : Fin 200) (e : E),
    dstTableB12 i.val e = caseTarget (caseB12 i) e := by decide +kernel

lemma sizeB12 : ∀ i : Fin 200, (lookupB12 i.val).size ≤ 5 →
    (lookupB12 i.val).size = 2 ∧
      (⟨caseKey (caseB12 i),caseKey_lt (caseB12 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB12 (i : Fin 200) : Certificate (caseB12 i) := by
  refine ⟨lookupB12 i.val,?_,sizeB12 i⟩
  have hv := tableB12_valid i
  rw [funext (srcB12_row i),funext (dstB12_row i)] at hv
  exact hv
lemma certificateInterval12 : FiniteIntervals.Covers CertificateAt 2400 2600 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 2400 200 (fun i _ => certificateB12 i)
#print axioms certificateInterval12
end Erdos184Work.FiveRows3

import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src2600 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2600 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2600_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2600_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,26,16,18]⟩
def cycle2600_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2600_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,26,14]⟩
def cycle2600_4 : CycleData E W := ⟨1,![8,16,12],![14,16,27]⟩
def cycle2600_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2600 : PartitionData E W := ⟨6,![cycle2600_0,cycle2600_1,cycle2600_2,cycle2600_3,cycle2600_4,cycle2600_5]⟩
lemma valid_data2600 : data2600.Valid src2600 dst2600 Finset.univ := by decide +kernel

def src2601 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2601 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2601_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2601_1 : CycleData E W := ⟨3,![2,14,17,7,6],![3,4,27,16,18]⟩
def cycle2601_2 : CycleData E W := ⟨3,![3,23,19,15,10],![4,8,38,6,26]⟩
def cycle2601_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle2601_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle2601_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2601 : PartitionData E W := ⟨6,![cycle2601_0,cycle2601_1,cycle2601_2,cycle2601_3,cycle2601_4,cycle2601_5]⟩
lemma valid_data2601 : data2601.Valid src2601 dst2601 Finset.univ := by decide +kernel

def src2602 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2602 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2602_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2602_1 : CycleData E W := ⟨3,![2,14,17,7,6],![3,4,27,16,18]⟩
def cycle2602_2 : CycleData E W := ⟨4,![3,20,21,19,15,10],![4,8,18,38,6,26]⟩
def cycle2602_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2602_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle2602_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2602 : PartitionData E W := ⟨6,![cycle2602_0,cycle2602_1,cycle2602_2,cycle2602_3,cycle2602_4,cycle2602_5]⟩
lemma valid_data2602 : data2602.Valid src2602 dst2602 Finset.univ := by decide +kernel

def src2603 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2603 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2603_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2603_1 : CycleData E W := ⟨3,![2,14,17,7,6],![3,4,27,16,18]⟩
def cycle2603_2 : CycleData E W := ⟨3,![3,23,19,15,10],![4,8,38,6,26]⟩
def cycle2603_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle2603_4 : CycleData E W := ⟨1,![8,16,11],![14,16,26]⟩
def cycle2603_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2603 : PartitionData E W := ⟨6,![cycle2603_0,cycle2603_1,cycle2603_2,cycle2603_3,cycle2603_4,cycle2603_5]⟩
lemma valid_data2603 : data2603.Valid src2603 dst2603 Finset.univ := by decide +kernel

def src2604 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2604 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2604_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2604_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2604_2 : CycleData E W := ⟨3,![4,23,16,11,9],![2,8,38,26,14]⟩
def cycle2604_3 : CycleData E W := ⟨2,![8,7,21,12],![14,16,18,28]⟩
def cycle2604_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2604_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2604 : PartitionData E W := ⟨6,![cycle2604_0,cycle2604_1,cycle2604_2,cycle2604_3,cycle2604_4,cycle2604_5]⟩
lemma valid_data2604 : data2604.Valid src2604 dst2604 Finset.univ := by decide +kernel

def src2605 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2605 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2605_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2605_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2605_2 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2605_3 : CycleData E W := ⟨3,![8,7,21,16,11],![14,16,18,38,26]⟩
def cycle2605_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2605_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2605 : PartitionData E W := ⟨6,![cycle2605_0,cycle2605_1,cycle2605_2,cycle2605_3,cycle2605_4,cycle2605_5]⟩
lemma valid_data2605 : data2605.Valid src2605 dst2605 Finset.univ := by decide +kernel

def src2606 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2606 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2606_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2606_1 : CycleData E W := ⟨3,![2,14,13,21,6],![3,4,27,28,18]⟩
def cycle2606_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2606_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle2606_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2606_5 : CycleData E W := ⟨3,![15,11,8,18,19],![6,26,14,16,27]⟩
def data2606 : PartitionData E W := ⟨6,![cycle2606_0,cycle2606_1,cycle2606_2,cycle2606_3,cycle2606_4,cycle2606_5]⟩
lemma valid_data2606 : data2606.Valid src2606 dst2606 Finset.univ := by decide +kernel

def src2607 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2607 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2607_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2607_1 : CycleData E W := ⟨3,![2,14,16,7,6],![3,4,27,16,18]⟩
def cycle2607_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2607_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle2607_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle2607_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2607 : PartitionData E W := ⟨6,![cycle2607_0,cycle2607_1,cycle2607_2,cycle2607_3,cycle2607_4,cycle2607_5]⟩
lemma valid_data2607 : data2607.Valid src2607 dst2607 Finset.univ := by decide +kernel

def src2608 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2608 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2608_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2608_1 : CycleData E W := ⟨3,![2,14,16,7,6],![3,4,27,16,18]⟩
def cycle2608_2 : CycleData E W := ⟨3,![3,20,21,18,10],![4,8,18,38,26]⟩
def cycle2608_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2608_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle2608_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2608 : PartitionData E W := ⟨6,![cycle2608_0,cycle2608_1,cycle2608_2,cycle2608_3,cycle2608_4,cycle2608_5]⟩
lemma valid_data2608 : data2608.Valid src2608 dst2608 Finset.univ := by decide +kernel

def src2609 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2609 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2609_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2609_1 : CycleData E W := ⟨3,![2,14,16,7,6],![3,4,27,16,18]⟩
def cycle2609_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2609_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle2609_4 : CycleData E W := ⟨1,![8,17,11],![14,16,26]⟩
def cycle2609_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2609 : PartitionData E W := ⟨6,![cycle2609_0,cycle2609_1,cycle2609_2,cycle2609_3,cycle2609_4,cycle2609_5]⟩
lemma valid_data2609 : data2609.Valid src2609 dst2609 Finset.univ := by decide +kernel

def src2610 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2610 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2610_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2610_1 : CycleData E W := ⟨3,![2,10,16,7,6],![3,4,26,16,18]⟩
def cycle2610_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2610_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle2610_4 : CycleData E W := ⟨1,![8,17,13],![14,16,27]⟩
def cycle2610_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2610 : PartitionData E W := ⟨6,![cycle2610_0,cycle2610_1,cycle2610_2,cycle2610_3,cycle2610_4,cycle2610_5]⟩
lemma valid_data2610 : data2610.Valid src2610 dst2610 Finset.univ := by decide +kernel

def src2611 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2611 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2611_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2611_1 : CycleData E W := ⟨3,![2,10,16,7,6],![3,4,26,16,18]⟩
def cycle2611_2 : CycleData E W := ⟨3,![3,20,21,18,14],![4,8,18,38,27]⟩
def cycle2611_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2611_4 : CycleData E W := ⟨1,![8,17,13],![14,16,27]⟩
def cycle2611_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2611 : PartitionData E W := ⟨6,![cycle2611_0,cycle2611_1,cycle2611_2,cycle2611_3,cycle2611_4,cycle2611_5]⟩
lemma valid_data2611 : data2611.Valid src2611 dst2611 Finset.univ := by decide +kernel

def src2612 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2612 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2612_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2612_1 : CycleData E W := ⟨3,![2,10,16,7,6],![3,4,26,16,18]⟩
def cycle2612_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2612_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle2612_4 : CycleData E W := ⟨1,![8,17,13],![14,16,27]⟩
def cycle2612_5 : CycleData E W := ⟨3,![15,11,21,22,19],![6,26,28,18,38]⟩
def data2612 : PartitionData E W := ⟨6,![cycle2612_0,cycle2612_1,cycle2612_2,cycle2612_3,cycle2612_4,cycle2612_5]⟩
lemma valid_data2612 : data2612.Valid src2612 dst2612 Finset.univ := by decide +kernel

def src2613 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2613 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2613_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2613_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2613_2 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle2613_3 : CycleData E W := ⟨2,![7,21,11,16],![16,18,28,26]⟩
def cycle2613_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2613_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2613 : PartitionData E W := ⟨6,![cycle2613_0,cycle2613_1,cycle2613_2,cycle2613_3,cycle2613_4,cycle2613_5]⟩
lemma valid_data2613 : data2613.Valid src2613 dst2613 Finset.univ := by decide +kernel

def src2614 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2614 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2614_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2614_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2614_2 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2614_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2614_4 : CycleData E W := ⟨3,![10,16,8,13,14],![4,26,16,14,27]⟩
def cycle2614_5 : CycleData E W := ⟨3,![15,11,22,18,19],![6,26,28,38,27]⟩
def data2614 : PartitionData E W := ⟨6,![cycle2614_0,cycle2614_1,cycle2614_2,cycle2614_3,cycle2614_4,cycle2614_5]⟩
lemma valid_data2614 : data2614.Valid src2614 dst2614 Finset.univ := by decide +kernel

def src2615 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2615 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2615_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2615_1 : CycleData E W := ⟨3,![2,10,11,21,6],![3,4,26,28,18]⟩
def cycle2615_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2615_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle2615_4 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2615_5 : CycleData E W := ⟨3,![15,16,8,13,19],![6,26,16,14,27]⟩
def data2615 : PartitionData E W := ⟨6,![cycle2615_0,cycle2615_1,cycle2615_2,cycle2615_3,cycle2615_4,cycle2615_5]⟩
lemma valid_data2615 : data2615.Valid src2615 dst2615 Finset.univ := by decide +kernel

def src2616 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2616 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2616_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2616_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,26,16,18]⟩
def cycle2616_2 : CycleData E W := ⟨3,![3,23,19,15,14],![4,8,38,6,27]⟩
def cycle2616_3 : CycleData E W := ⟨3,![4,20,21,12,9],![2,8,18,28,14]⟩
def cycle2616_4 : CycleData E W := ⟨1,![8,16,13],![14,16,27]⟩
def cycle2616_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2616 : PartitionData E W := ⟨6,![cycle2616_0,cycle2616_1,cycle2616_2,cycle2616_3,cycle2616_4,cycle2616_5]⟩
lemma valid_data2616 : data2616.Valid src2616 dst2616 Finset.univ := by decide +kernel

def src2617 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2617 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2617_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2617_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,26,16,18]⟩
def cycle2617_2 : CycleData E W := ⟨4,![3,20,21,19,15,14],![4,8,18,38,6,27]⟩
def cycle2617_3 : CycleData E W := ⟨2,![4,23,12,9],![2,8,28,14]⟩
def cycle2617_4 : CycleData E W := ⟨1,![8,16,13],![14,16,27]⟩
def cycle2617_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2617 : PartitionData E W := ⟨6,![cycle2617_0,cycle2617_1,cycle2617_2,cycle2617_3,cycle2617_4,cycle2617_5]⟩
lemma valid_data2617 : data2617.Valid src2617 dst2617 Finset.univ := by decide +kernel

def src2618 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2618 : E → W := ![6,3,4,8,2,3,18,16,14,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2618_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2618_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,26,16,18]⟩
def cycle2618_2 : CycleData E W := ⟨3,![3,23,19,15,14],![4,8,38,6,27]⟩
def cycle2618_3 : CycleData E W := ⟨2,![4,20,12,9],![2,8,28,14]⟩
def cycle2618_4 : CycleData E W := ⟨1,![8,16,13],![14,16,27]⟩
def cycle2618_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data2618 : PartitionData E W := ⟨6,![cycle2618_0,cycle2618_1,cycle2618_2,cycle2618_3,cycle2618_4,cycle2618_5]⟩
lemma valid_data2618 : data2618.Valid src2618 dst2618 Finset.univ := by decide +kernel

def src2619 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2619 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2619_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2619_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,27,16,18]⟩
def cycle2619_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2619_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,27,14]⟩
def cycle2619_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2619_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2619 : PartitionData E W := ⟨6,![cycle2619_0,cycle2619_1,cycle2619_2,cycle2619_3,cycle2619_4,cycle2619_5]⟩
lemma valid_data2619 : data2619.Valid src2619 dst2619 Finset.univ := by decide +kernel

def src2620 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2620 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2620_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2620_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,27,16,18]⟩
def cycle2620_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2620_3 : CycleData E W := ⟨4,![4,20,21,18,11,9],![2,8,18,38,27,14]⟩
def cycle2620_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2620_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2620 : PartitionData E W := ⟨6,![cycle2620_0,cycle2620_1,cycle2620_2,cycle2620_3,cycle2620_4,cycle2620_5]⟩
lemma valid_data2620 : data2620.Valid src2620 dst2620 Finset.univ := by decide +kernel

def src2621 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2621 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2621_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2621_1 : CycleData E W := ⟨3,![2,10,17,7,6],![3,4,27,16,18]⟩
def cycle2621_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2621_3 : CycleData E W := ⟨3,![4,23,18,11,9],![2,8,38,27,14]⟩
def cycle2621_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2621_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2621 : PartitionData E W := ⟨6,![cycle2621_0,cycle2621_1,cycle2621_2,cycle2621_3,cycle2621_4,cycle2621_5]⟩
lemma valid_data2621 : data2621.Valid src2621 dst2621 Finset.univ := by decide +kernel

def src2622 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2622 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2622_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2622_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2622_2 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle2622_3 : CycleData E W := ⟨2,![7,21,13,16],![16,18,28,26]⟩
def cycle2622_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2622_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2622 : PartitionData E W := ⟨6,![cycle2622_0,cycle2622_1,cycle2622_2,cycle2622_3,cycle2622_4,cycle2622_5]⟩
lemma valid_data2622 : data2622.Valid src2622 dst2622 Finset.univ := by decide +kernel

def src2623 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2623 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2623_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2623_1 : CycleData E W := ⟨2,![2,3,20,6],![3,4,8,18]⟩
def cycle2623_2 : CycleData E W := ⟨3,![4,23,13,12,9],![2,8,28,26,14]⟩
def cycle2623_3 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2623_4 : CycleData E W := ⟨3,![15,16,8,11,19],![6,26,16,14,27]⟩
def cycle2623_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data2623 : PartitionData E W := ⟨6,![cycle2623_0,cycle2623_1,cycle2623_2,cycle2623_3,cycle2623_4,cycle2623_5]⟩
lemma valid_data2623 : data2623.Valid src2623 dst2623 Finset.univ := by decide +kernel

def src2624 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2624 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2624_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2624_1 : CycleData E W := ⟨2,![2,14,21,6],![3,4,28,18]⟩
def cycle2624_2 : CycleData E W := ⟨3,![4,3,10,11,9],![2,8,4,27,14]⟩
def cycle2624_3 : CycleData E W := ⟨1,![7,22,17],![16,18,38]⟩
def cycle2624_4 : CycleData E W := ⟨1,![8,16,12],![14,16,26]⟩
def cycle2624_5 : CycleData E W := ⟨4,![15,13,20,23,18,19],![6,26,28,8,38,27]⟩
def data2624 : PartitionData E W := ⟨6,![cycle2624_0,cycle2624_1,cycle2624_2,cycle2624_3,cycle2624_4,cycle2624_5]⟩
lemma valid_data2624 : data2624.Valid src2624 dst2624 Finset.univ := by decide +kernel

def src2625 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2625 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2625_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2625_1 : CycleData E W := ⟨3,![2,10,18,7,6],![3,4,27,16,18]⟩
def cycle2625_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2625_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle2625_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2625_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2625 : PartitionData E W := ⟨6,![cycle2625_0,cycle2625_1,cycle2625_2,cycle2625_3,cycle2625_4,cycle2625_5]⟩
lemma valid_data2625 : data2625.Valid src2625 dst2625 Finset.univ := by decide +kernel

def src2626 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2626 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2626_0 : CycleData E W := ⟨2,![0,15,12,9],![2,6,26,14]⟩
def cycle2626_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,27,4]⟩
def cycle2626_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2626_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,3]⟩
def cycle2626_4 : CycleData E W := ⟨1,![7,21,17],![16,18,38]⟩
def cycle2626_5 : CycleData E W := ⟨1,![8,18,11],![14,16,27]⟩
def cycle2626_6 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2626 : PartitionData E W := ⟨7,![cycle2626_0,cycle2626_1,cycle2626_2,cycle2626_3,cycle2626_4,cycle2626_5,cycle2626_6]⟩
lemma valid_data2626 : data2626.Valid src2626 dst2626 Finset.univ := by decide +kernel

def src2627 : E → W := ![2,6,3,4,8,2,3,18,16,14,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2627 : E → W := ![6,3,4,8,2,3,18,16,14,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2627_0 : CycleData E W := ⟨1,![0,1,5],![2,6,3]⟩
def cycle2627_1 : CycleData E W := ⟨3,![2,10,18,7,6],![3,4,27,16,18]⟩
def cycle2627_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2627_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,14]⟩
def cycle2627_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2627_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2627 : PartitionData E W := ⟨6,![cycle2627_0,cycle2627_1,cycle2627_2,cycle2627_3,cycle2627_4,cycle2627_5]⟩
lemma valid_data2627 : data2627.Valid src2627 dst2627 Finset.univ := by decide +kernel

def src2628 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst2628 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2628_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2628_1 : CycleData E W := ⟨4,![2,10,11,16,17,7],![3,4,14,26,38,16]⟩
def cycle2628_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2628_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2628_4 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2628_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2628 : PartitionData E W := ⟨6,![cycle2628_0,cycle2628_1,cycle2628_2,cycle2628_3,cycle2628_4,cycle2628_5]⟩
lemma valid_data2628 : data2628.Valid src2628 dst2628 Finset.univ := by decide +kernel

def src2629 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst2629 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2629_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2629_1 : CycleData E W := ⟨2,![1,19,18,7],![3,6,27,16]⟩
def cycle2629_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2629_3 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2629_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2629_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2629_6 : CycleData E W := ⟨2,![12,13,22,16],![26,27,28,38]⟩
def data2629 : PartitionData E W := ⟨7,![cycle2629_0,cycle2629_1,cycle2629_2,cycle2629_3,cycle2629_4,cycle2629_5,cycle2629_6]⟩
lemma valid_data2629 : data2629.Valid src2629 dst2629 Finset.univ := by decide +kernel

def src2630 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst2630 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2630_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2630_1 : CycleData E W := ⟨4,![2,10,11,16,17,7],![3,4,14,26,38,16]⟩
def cycle2630_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2630_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2630_4 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2630_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2630 : PartitionData E W := ⟨6,![cycle2630_0,cycle2630_1,cycle2630_2,cycle2630_3,cycle2630_4,cycle2630_5]⟩
lemma valid_data2630 : data2630.Valid src2630 dst2630 Finset.univ := by decide +kernel

def src2631 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst2631 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2631_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2631_1 : CycleData E W := ⟨3,![2,10,11,17,7],![3,4,14,26,16]⟩
def cycle2631_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2631_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2631_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2631_5 : CycleData E W := ⟨2,![15,12,18,19],![6,27,26,38]⟩
def data2631 : PartitionData E W := ⟨6,![cycle2631_0,cycle2631_1,cycle2631_2,cycle2631_3,cycle2631_4,cycle2631_5]⟩
lemma valid_data2631 : data2631.Valid src2631 dst2631 Finset.univ := by decide +kernel

def src2632 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst2632 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2632_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2632_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,14,26,27,16]⟩
def cycle2632_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2632_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2632_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2632_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2632 : PartitionData E W := ⟨6,![cycle2632_0,cycle2632_1,cycle2632_2,cycle2632_3,cycle2632_4,cycle2632_5]⟩
lemma valid_data2632 : data2632.Valid src2632 dst2632 Finset.univ := by decide +kernel

def src2633 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst2633 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2633_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2633_1 : CycleData E W := ⟨3,![2,10,11,17,7],![3,4,14,26,16]⟩
def cycle2633_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2633_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2633_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2633_5 : CycleData E W := ⟨2,![15,12,18,19],![6,27,26,38]⟩
def data2633 : PartitionData E W := ⟨6,![cycle2633_0,cycle2633_1,cycle2633_2,cycle2633_3,cycle2633_4,cycle2633_5]⟩
lemma valid_data2633 : data2633.Valid src2633 dst2633 Finset.univ := by decide +kernel

def src2634 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst2634 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2634_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2634_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,14,26,16]⟩
def cycle2634_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2634_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2634_4 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def cycle2634_5 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def data2634 : PartitionData E W := ⟨6,![cycle2634_0,cycle2634_1,cycle2634_2,cycle2634_3,cycle2634_4,cycle2634_5]⟩
lemma valid_data2634 : data2634.Valid src2634 dst2634 Finset.univ := by decide +kernel

def src2635 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst2635 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2635_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2635_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,14,26,16]⟩
def cycle2635_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle2635_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2635_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2635_5 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def data2635 : PartitionData E W := ⟨6,![cycle2635_0,cycle2635_1,cycle2635_2,cycle2635_3,cycle2635_4,cycle2635_5]⟩
lemma valid_data2635 : data2635.Valid src2635 dst2635 Finset.univ := by decide +kernel

def src2636 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst2636 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2636_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2636_1 : CycleData E W := ⟨3,![1,19,18,17,7],![3,6,38,27,16]⟩
def cycle2636_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2636_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle2636_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2636_5 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def data2636 : PartitionData E W := ⟨6,![cycle2636_0,cycle2636_1,cycle2636_2,cycle2636_3,cycle2636_4,cycle2636_5]⟩
lemma valid_data2636 : data2636.Valid src2636 dst2636 Finset.univ := by decide +kernel

def src2637 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst2637 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle2637_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2637_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,14,26,16]⟩
def cycle2637_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2637_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2637_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2637_5 : CycleData E W := ⟨2,![15,12,13,19],![6,26,28,27]⟩
def data2637 : PartitionData E W := ⟨6,![cycle2637_0,cycle2637_1,cycle2637_2,cycle2637_3,cycle2637_4,cycle2637_5]⟩
lemma valid_data2637 : data2637.Valid src2637 dst2637 Finset.univ := by decide +kernel

def src2638 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst2638 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle2638_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2638_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,14,26,16]⟩
def cycle2638_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle2638_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2638_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2638_5 : CycleData E W := ⟨3,![15,12,22,18,19],![6,26,28,38,27]⟩
def data2638 : PartitionData E W := ⟨6,![cycle2638_0,cycle2638_1,cycle2638_2,cycle2638_3,cycle2638_4,cycle2638_5]⟩
lemma valid_data2638 : data2638.Valid src2638 dst2638 Finset.univ := by decide +kernel

def src2639 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst2639 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle2639_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2639_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,14,26,16]⟩
def cycle2639_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2639_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2639_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2639_5 : CycleData E W := ⟨2,![15,12,13,19],![6,26,28,27]⟩
def data2639 : PartitionData E W := ⟨6,![cycle2639_0,cycle2639_1,cycle2639_2,cycle2639_3,cycle2639_4,cycle2639_5]⟩
lemma valid_data2639 : data2639.Valid src2639 dst2639 Finset.univ := by decide +kernel

def src2640 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst2640 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2640_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2640_1 : CycleData E W := ⟨2,![2,14,18,7],![3,4,27,16]⟩
def cycle2640_2 : CycleData E W := ⟨3,![3,23,16,11,10],![4,8,38,26,14]⟩
def cycle2640_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2640_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2640_5 : CycleData E W := ⟨2,![15,12,13,19],![6,26,28,27]⟩
def data2640 : PartitionData E W := ⟨6,![cycle2640_0,cycle2640_1,cycle2640_2,cycle2640_3,cycle2640_4,cycle2640_5]⟩
lemma valid_data2640 : data2640.Valid src2640 dst2640 Finset.univ := by decide +kernel

def src2641 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst2641 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2641_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2641_1 : CycleData E W := ⟨2,![1,19,18,7],![3,6,27,16]⟩
def cycle2641_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2641_3 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle2641_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2641_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2641_6 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2641 : PartitionData E W := ⟨7,![cycle2641_0,cycle2641_1,cycle2641_2,cycle2641_3,cycle2641_4,cycle2641_5,cycle2641_6]⟩
lemma valid_data2641 : data2641.Valid src2641 dst2641 Finset.univ := by decide +kernel

def src2642 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst2642 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2642_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2642_1 : CycleData E W := ⟨2,![2,14,18,7],![3,4,27,16]⟩
def cycle2642_2 : CycleData E W := ⟨3,![3,23,16,11,10],![4,8,38,26,14]⟩
def cycle2642_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2642_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2642_5 : CycleData E W := ⟨2,![15,12,13,19],![6,26,28,27]⟩
def data2642 : PartitionData E W := ⟨6,![cycle2642_0,cycle2642_1,cycle2642_2,cycle2642_3,cycle2642_4,cycle2642_5]⟩
lemma valid_data2642 : data2642.Valid src2642 dst2642 Finset.univ := by decide +kernel

def src2643 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst2643 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2643_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2643_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2643_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,26,14]⟩
def cycle2643_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2643_4 : CycleData E W := ⟨2,![8,21,12,17],![16,18,28,26]⟩
def cycle2643_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2643 : PartitionData E W := ⟨6,![cycle2643_0,cycle2643_1,cycle2643_2,cycle2643_3,cycle2643_4,cycle2643_5]⟩
lemma valid_data2643 : data2643.Valid src2643 dst2643 Finset.univ := by decide +kernel

def src2644 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst2644 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2644_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2644_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2644_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,26,14]⟩
def cycle2644_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2644_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2644_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2644 : PartitionData E W := ⟨6,![cycle2644_0,cycle2644_1,cycle2644_2,cycle2644_3,cycle2644_4,cycle2644_5]⟩
lemma valid_data2644 : data2644.Valid src2644 dst2644 Finset.univ := by decide +kernel

def src2645 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst2645 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2645_0 : CycleData E W := ⟨3,![0,19,18,11,5],![2,6,38,26,14]⟩
def cycle2645_1 : CycleData E W := ⟨2,![1,15,16,7],![3,6,27,16]⟩
def cycle2645_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2645_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle2645_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2645_5 : CycleData E W := ⟨2,![8,21,12,17],![16,18,28,26]⟩
def data2645 : PartitionData E W := ⟨6,![cycle2645_0,cycle2645_1,cycle2645_2,cycle2645_3,cycle2645_4,cycle2645_5]⟩
lemma valid_data2645 : data2645.Valid src2645 dst2645 Finset.univ := by decide +kernel

def src2646 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst2646 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2646_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2646_1 : CycleData E W := ⟨3,![2,10,11,17,7],![3,4,14,27,16]⟩
def cycle2646_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2646_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2646_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2646_5 : CycleData E W := ⟨2,![15,12,18,19],![6,26,27,38]⟩
def data2646 : PartitionData E W := ⟨6,![cycle2646_0,cycle2646_1,cycle2646_2,cycle2646_3,cycle2646_4,cycle2646_5]⟩
lemma valid_data2646 : data2646.Valid src2646 dst2646 Finset.univ := by decide +kernel

def src2647 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst2647 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2647_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2647_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,14,27,26,16]⟩
def cycle2647_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2647_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2647_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2647_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2647 : PartitionData E W := ⟨6,![cycle2647_0,cycle2647_1,cycle2647_2,cycle2647_3,cycle2647_4,cycle2647_5]⟩
lemma valid_data2647 : data2647.Valid src2647 dst2647 Finset.univ := by decide +kernel

def src2648 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst2648 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2648_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2648_1 : CycleData E W := ⟨3,![2,10,11,17,7],![3,4,14,27,16]⟩
def cycle2648_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2648_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2648_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2648_5 : CycleData E W := ⟨2,![15,12,18,19],![6,26,27,38]⟩
def data2648 : PartitionData E W := ⟨6,![cycle2648_0,cycle2648_1,cycle2648_2,cycle2648_3,cycle2648_4,cycle2648_5]⟩
lemma valid_data2648 : data2648.Valid src2648 dst2648 Finset.univ := by decide +kernel

def src2649 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst2649 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2649_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2649_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,26,16]⟩
def cycle2649_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,27,14]⟩
def cycle2649_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2649_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2649_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2649 : PartitionData E W := ⟨6,![cycle2649_0,cycle2649_1,cycle2649_2,cycle2649_3,cycle2649_4,cycle2649_5]⟩
lemma valid_data2649 : data2649.Valid src2649 dst2649 Finset.univ := by decide +kernel

def src2650 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst2650 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2650_0 : CycleData E W := ⟨2,![0,19,11,5],![2,6,27,14]⟩
def cycle2650_1 : CycleData E W := ⟨2,![1,15,16,7],![3,6,26,16]⟩
def cycle2650_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2650_3 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2650_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2650_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2650_6 : CycleData E W := ⟨2,![12,18,22,13],![26,27,38,28]⟩
def data2650 : PartitionData E W := ⟨7,![cycle2650_0,cycle2650_1,cycle2650_2,cycle2650_3,cycle2650_4,cycle2650_5,cycle2650_6]⟩
lemma valid_data2650 : data2650.Valid src2650 dst2650 Finset.univ := by decide +kernel

def src2651 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst2651 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2651_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2651_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,26,16]⟩
def cycle2651_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,27,14]⟩
def cycle2651_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2651_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2651_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2651 : PartitionData E W := ⟨6,![cycle2651_0,cycle2651_1,cycle2651_2,cycle2651_3,cycle2651_4,cycle2651_5]⟩
lemma valid_data2651 : data2651.Valid src2651 dst2651 Finset.univ := by decide +kernel

def src2652 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst2652 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle2652_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2652_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,26,16]⟩
def cycle2652_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,27,14]⟩
def cycle2652_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2652_4 : CycleData E W := ⟨2,![8,21,12,17],![16,18,28,27]⟩
def cycle2652_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2652 : PartitionData E W := ⟨6,![cycle2652_0,cycle2652_1,cycle2652_2,cycle2652_3,cycle2652_4,cycle2652_5]⟩
lemma valid_data2652 : data2652.Valid src2652 dst2652 Finset.univ := by decide +kernel

def src2653 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst2653 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle2653_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2653_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,26,16]⟩
def cycle2653_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,27,14]⟩
def cycle2653_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2653_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2653_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2653 : PartitionData E W := ⟨6,![cycle2653_0,cycle2653_1,cycle2653_2,cycle2653_3,cycle2653_4,cycle2653_5]⟩
lemma valid_data2653 : data2653.Valid src2653 dst2653 Finset.univ := by decide +kernel

def src2654 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst2654 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle2654_0 : CycleData E W := ⟨3,![0,19,18,11,5],![2,6,38,27,14]⟩
def cycle2654_1 : CycleData E W := ⟨2,![1,15,16,7],![3,6,26,16]⟩
def cycle2654_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2654_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,26]⟩
def cycle2654_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2654_5 : CycleData E W := ⟨2,![8,21,12,17],![16,18,28,27]⟩
def data2654 : PartitionData E W := ⟨6,![cycle2654_0,cycle2654_1,cycle2654_2,cycle2654_3,cycle2654_4,cycle2654_5]⟩
lemma valid_data2654 : data2654.Valid src2654 dst2654 Finset.univ := by decide +kernel

def src2655 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst2655 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle2655_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2655_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,26,16]⟩
def cycle2655_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,27,14]⟩
def cycle2655_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2655_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2655_5 : CycleData E W := ⟨2,![15,13,12,19],![6,26,28,27]⟩
def data2655 : PartitionData E W := ⟨6,![cycle2655_0,cycle2655_1,cycle2655_2,cycle2655_3,cycle2655_4,cycle2655_5]⟩
lemma valid_data2655 : data2655.Valid src2655 dst2655 Finset.univ := by decide +kernel

def src2656 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst2656 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle2656_0 : CycleData E W := ⟨2,![0,19,11,5],![2,6,27,14]⟩
def cycle2656_1 : CycleData E W := ⟨2,![1,15,16,7],![3,6,26,16]⟩
def cycle2656_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2656_3 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,26]⟩
def cycle2656_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2656_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2656_6 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2656 : PartitionData E W := ⟨7,![cycle2656_0,cycle2656_1,cycle2656_2,cycle2656_3,cycle2656_4,cycle2656_5,cycle2656_6]⟩
lemma valid_data2656 : data2656.Valid src2656 dst2656 Finset.univ := by decide +kernel

def src2657 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst2657 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle2657_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2657_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,26,16]⟩
def cycle2657_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,27,14]⟩
def cycle2657_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2657_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2657_5 : CycleData E W := ⟨2,![15,13,12,19],![6,26,28,27]⟩
def data2657 : PartitionData E W := ⟨6,![cycle2657_0,cycle2657_1,cycle2657_2,cycle2657_3,cycle2657_4,cycle2657_5]⟩
lemma valid_data2657 : data2657.Valid src2657 dst2657 Finset.univ := by decide +kernel

def src2658 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst2658 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle2658_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2658_1 : CycleData E W := ⟨3,![2,10,11,18,7],![3,4,14,27,16]⟩
def cycle2658_2 : CycleData E W := ⟨2,![3,23,16,14],![4,8,38,26]⟩
def cycle2658_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2658_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2658_5 : CycleData E W := ⟨2,![15,13,12,19],![6,26,28,27]⟩
def data2658 : PartitionData E W := ⟨6,![cycle2658_0,cycle2658_1,cycle2658_2,cycle2658_3,cycle2658_4,cycle2658_5]⟩
lemma valid_data2658 : data2658.Valid src2658 dst2658 Finset.univ := by decide +kernel

def src2659 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst2659 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle2659_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2659_1 : CycleData E W := ⟨3,![2,10,11,18,7],![3,4,14,27,16]⟩
def cycle2659_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,26]⟩
def cycle2659_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2659_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2659_5 : CycleData E W := ⟨3,![15,16,22,12,19],![6,26,38,28,27]⟩
def data2659 : PartitionData E W := ⟨6,![cycle2659_0,cycle2659_1,cycle2659_2,cycle2659_3,cycle2659_4,cycle2659_5]⟩
lemma valid_data2659 : data2659.Valid src2659 dst2659 Finset.univ := by decide +kernel

def src2660 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst2660 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle2660_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2660_1 : CycleData E W := ⟨3,![2,10,11,18,7],![3,4,14,27,16]⟩
def cycle2660_2 : CycleData E W := ⟨2,![3,23,16,14],![4,8,38,26]⟩
def cycle2660_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2660_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2660_5 : CycleData E W := ⟨2,![15,13,12,19],![6,26,28,27]⟩
def data2660 : PartitionData E W := ⟨6,![cycle2660_0,cycle2660_1,cycle2660_2,cycle2660_3,cycle2660_4,cycle2660_5]⟩
lemma valid_data2660 : data2660.Valid src2660 dst2660 Finset.univ := by decide +kernel

def src2661 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst2661 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle2661_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2661_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,14,27,16]⟩
def cycle2661_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,26]⟩
def cycle2661_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2661_4 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,26]⟩
def cycle2661_5 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def data2661 : PartitionData E W := ⟨6,![cycle2661_0,cycle2661_1,cycle2661_2,cycle2661_3,cycle2661_4,cycle2661_5]⟩
lemma valid_data2661 : data2661.Valid src2661 dst2661 Finset.univ := by decide +kernel

def src2662 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst2662 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle2662_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2662_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,14,27,16]⟩
def cycle2662_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,26]⟩
def cycle2662_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2662_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2662_5 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def data2662 : PartitionData E W := ⟨6,![cycle2662_0,cycle2662_1,cycle2662_2,cycle2662_3,cycle2662_4,cycle2662_5]⟩
lemma valid_data2662 : data2662.Valid src2662 dst2662 Finset.univ := by decide +kernel

def src2663 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst2663 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle2663_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,27,14]⟩
def cycle2663_1 : CycleData E W := ⟨3,![1,19,18,17,7],![3,6,38,26,16]⟩
def cycle2663_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2663_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,26]⟩
def cycle2663_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2663_5 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,27]⟩
def data2663 : PartitionData E W := ⟨6,![cycle2663_0,cycle2663_1,cycle2663_2,cycle2663_3,cycle2663_4,cycle2663_5]⟩
lemma valid_data2663 : data2663.Valid src2663 dst2663 Finset.univ := by decide +kernel

def src2664 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst2664 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle2664_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2664_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2664_2 : CycleData E W := ⟨3,![3,23,22,11,10],![4,8,38,28,14]⟩
def cycle2664_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2664_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle2664_5 : CycleData E W := ⟨2,![15,13,18,19],![6,26,27,38]⟩
def data2664 : PartitionData E W := ⟨6,![cycle2664_0,cycle2664_1,cycle2664_2,cycle2664_3,cycle2664_4,cycle2664_5]⟩
lemma valid_data2664 : data2664.Valid src2664 dst2664 Finset.univ := by decide +kernel

def src2665 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst2665 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle2665_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2665_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,27,26,16]⟩
def cycle2665_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,14]⟩
def cycle2665_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2665_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2665_5 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def data2665 : PartitionData E W := ⟨6,![cycle2665_0,cycle2665_1,cycle2665_2,cycle2665_3,cycle2665_4,cycle2665_5]⟩
lemma valid_data2665 : data2665.Valid src2665 dst2665 Finset.univ := by decide +kernel

def src2666 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst2666 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle2666_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2666_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2666_2 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,14]⟩
def cycle2666_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2666_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle2666_5 : CycleData E W := ⟨2,![15,13,18,19],![6,26,27,38]⟩
def data2666 : PartitionData E W := ⟨6,![cycle2666_0,cycle2666_1,cycle2666_2,cycle2666_3,cycle2666_4,cycle2666_5]⟩
lemma valid_data2666 : data2666.Valid src2666 dst2666 Finset.univ := by decide +kernel

def src2667 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst2667 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle2667_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2667_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,14,28,26,16]⟩
def cycle2667_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2667_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2667_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2667_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2667 : PartitionData E W := ⟨6,![cycle2667_0,cycle2667_1,cycle2667_2,cycle2667_3,cycle2667_4,cycle2667_5]⟩
lemma valid_data2667 : data2667.Valid src2667 dst2667 Finset.univ := by decide +kernel

def src2668 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst2668 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle2668_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2668_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,14,28,26,16]⟩
def cycle2668_2 : CycleData E W := ⟨3,![3,23,22,18,14],![4,8,28,38,27]⟩
def cycle2668_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2668_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2668_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2668 : PartitionData E W := ⟨6,![cycle2668_0,cycle2668_1,cycle2668_2,cycle2668_3,cycle2668_4,cycle2668_5]⟩
lemma valid_data2668 : data2668.Valid src2668 dst2668 Finset.univ := by decide +kernel

def src2669 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst2669 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle2669_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2669_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,14,28,26,16]⟩
def cycle2669_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2669_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2669_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2669_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2669 : PartitionData E W := ⟨6,![cycle2669_0,cycle2669_1,cycle2669_2,cycle2669_3,cycle2669_4,cycle2669_5]⟩
lemma valid_data2669 : data2669.Valid src2669 dst2669 Finset.univ := by decide +kernel

def src2670 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst2670 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle2670_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2670_1 : CycleData E W := ⟨3,![2,14,16,17,7],![3,4,26,38,16]⟩
def cycle2670_2 : CycleData E W := ⟨3,![3,23,22,11,10],![4,8,38,28,14]⟩
def cycle2670_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2670_4 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle2670_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2670 : PartitionData E W := ⟨6,![cycle2670_0,cycle2670_1,cycle2670_2,cycle2670_3,cycle2670_4,cycle2670_5]⟩
lemma valid_data2670 : data2670.Valid src2670 dst2670 Finset.univ := by decide +kernel

def src2671 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst2671 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle2671_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2671_1 : CycleData E W := ⟨3,![2,14,16,17,7],![3,4,26,38,16]⟩
def cycle2671_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,14]⟩
def cycle2671_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2671_4 : CycleData E W := ⟨3,![8,21,22,12,18],![16,18,38,28,27]⟩
def cycle2671_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2671 : PartitionData E W := ⟨6,![cycle2671_0,cycle2671_1,cycle2671_2,cycle2671_3,cycle2671_4,cycle2671_5]⟩
lemma valid_data2671 : data2671.Valid src2671 dst2671 Finset.univ := by decide +kernel

def src2672 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst2672 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle2672_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2672_1 : CycleData E W := ⟨3,![2,14,16,17,7],![3,4,26,38,16]⟩
def cycle2672_2 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,14]⟩
def cycle2672_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2672_4 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle2672_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2672 : PartitionData E W := ⟨6,![cycle2672_0,cycle2672_1,cycle2672_2,cycle2672_3,cycle2672_4,cycle2672_5]⟩
lemma valid_data2672 : data2672.Valid src2672 dst2672 Finset.univ := by decide +kernel

def src2673 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst2673 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle2673_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2673_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,26,16]⟩
def cycle2673_2 : CycleData E W := ⟨3,![3,23,22,11,10],![4,8,38,28,14]⟩
def cycle2673_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2673_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,27]⟩
def cycle2673_5 : CycleData E W := ⟨2,![15,13,18,19],![6,27,26,38]⟩
def data2673 : PartitionData E W := ⟨6,![cycle2673_0,cycle2673_1,cycle2673_2,cycle2673_3,cycle2673_4,cycle2673_5]⟩
lemma valid_data2673 : data2673.Valid src2673 dst2673 Finset.univ := by decide +kernel

def src2674 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst2674 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle2674_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2674_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,26,27,16]⟩
def cycle2674_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,14]⟩
def cycle2674_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2674_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2674_5 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def data2674 : PartitionData E W := ⟨6,![cycle2674_0,cycle2674_1,cycle2674_2,cycle2674_3,cycle2674_4,cycle2674_5]⟩
lemma valid_data2674 : data2674.Valid src2674 dst2674 Finset.univ := by decide +kernel

def src2675 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst2675 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle2675_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2675_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,26,16]⟩
def cycle2675_2 : CycleData E W := ⟨2,![3,20,11,10],![4,8,28,14]⟩
def cycle2675_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2675_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,27]⟩
def cycle2675_5 : CycleData E W := ⟨2,![15,13,18,19],![6,27,26,38]⟩
def data2675 : PartitionData E W := ⟨6,![cycle2675_0,cycle2675_1,cycle2675_2,cycle2675_3,cycle2675_4,cycle2675_5]⟩
lemma valid_data2675 : data2675.Valid src2675 dst2675 Finset.univ := by decide +kernel

def src2676 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst2676 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle2676_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2676_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2676_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2676_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2676_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,27]⟩
def cycle2676_5 : CycleData E W := ⟨2,![11,17,18,12],![14,26,38,27]⟩
def data2676 : PartitionData E W := ⟨6,![cycle2676_0,cycle2676_1,cycle2676_2,cycle2676_3,cycle2676_4,cycle2676_5]⟩
lemma valid_data2676 : data2676.Valid src2676 dst2676 Finset.univ := by decide +kernel

def src2677 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst2677 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle2677_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,27,14]⟩
def cycle2677_1 : CycleData E W := ⟨1,![1,15,7],![3,6,16]⟩
def cycle2677_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle2677_3 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2677_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2677_5 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle2677_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2677 : PartitionData E W := ⟨7,![cycle2677_0,cycle2677_1,cycle2677_2,cycle2677_3,cycle2677_4,cycle2677_5,cycle2677_6]⟩
lemma valid_data2677 : data2677.Valid src2677 dst2677 Finset.univ := by decide +kernel

def src2678 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst2678 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle2678_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2678_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2678_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2678_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2678_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,27]⟩
def cycle2678_5 : CycleData E W := ⟨2,![11,17,18,12],![14,26,38,27]⟩
def data2678 : PartitionData E W := ⟨6,![cycle2678_0,cycle2678_1,cycle2678_2,cycle2678_3,cycle2678_4,cycle2678_5]⟩
lemma valid_data2678 : data2678.Valid src2678 dst2678 Finset.univ := by decide +kernel

def src2679 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst2679 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle2679_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2679_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,27,16]⟩
def cycle2679_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2679_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2679_4 : CycleData E W := ⟨3,![15,8,21,22,19],![6,16,18,28,38]⟩
def cycle2679_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2679 : PartitionData E W := ⟨6,![cycle2679_0,cycle2679_1,cycle2679_2,cycle2679_3,cycle2679_4,cycle2679_5]⟩
lemma valid_data2679 : data2679.Valid src2679 dst2679 Finset.univ := by decide +kernel

def src2680 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst2680 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle2680_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2680_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,26,14,27,16]⟩
def cycle2680_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2680_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2680_4 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2680_5 : CycleData E W := ⟨2,![17,13,22,18],![26,27,28,38]⟩
def data2680 : PartitionData E W := ⟨6,![cycle2680_0,cycle2680_1,cycle2680_2,cycle2680_3,cycle2680_4,cycle2680_5]⟩
lemma valid_data2680 : data2680.Valid src2680 dst2680 Finset.univ := by decide +kernel

def src2681 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst2681 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle2681_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2681_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,27,16]⟩
def cycle2681_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2681_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2681_4 : CycleData E W := ⟨2,![15,8,22,19],![6,16,18,38]⟩
def cycle2681_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2681 : PartitionData E W := ⟨6,![cycle2681_0,cycle2681_1,cycle2681_2,cycle2681_3,cycle2681_4,cycle2681_5]⟩
lemma valid_data2681 : data2681.Valid src2681 dst2681 Finset.univ := by decide +kernel

def src2682 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst2682 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle2682_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2682_1 : CycleData E W := ⟨3,![2,10,19,15,7],![3,4,26,6,16]⟩
def cycle2682_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2682_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2682_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2682_5 : CycleData E W := ⟨2,![11,18,17,12],![14,26,38,27]⟩
def data2682 : PartitionData E W := ⟨6,![cycle2682_0,cycle2682_1,cycle2682_2,cycle2682_3,cycle2682_4,cycle2682_5]⟩
lemma valid_data2682 : data2682.Valid src2682 dst2682 Finset.univ := by decide +kernel

def src2683 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst2683 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle2683_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2683_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,26,14,27,16]⟩
def cycle2683_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2683_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2683_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,26]⟩
def cycle2683_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2683 : PartitionData E W := ⟨6,![cycle2683_0,cycle2683_1,cycle2683_2,cycle2683_3,cycle2683_4,cycle2683_5]⟩
lemma valid_data2683 : data2683.Valid src2683 dst2683 Finset.univ := by decide +kernel

def src2684 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst2684 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle2684_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2684_1 : CycleData E W := ⟨3,![2,10,19,15,7],![3,4,26,6,16]⟩
def cycle2684_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2684_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2684_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2684_5 : CycleData E W := ⟨2,![11,18,17,12],![14,26,38,27]⟩
def data2684 : PartitionData E W := ⟨6,![cycle2684_0,cycle2684_1,cycle2684_2,cycle2684_3,cycle2684_4,cycle2684_5]⟩
lemma valid_data2684 : data2684.Valid src2684 dst2684 Finset.univ := by decide +kernel

def src2685 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst2685 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle2685_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2685_1 : CycleData E W := ⟨3,![2,10,17,16,7],![3,4,26,38,16]⟩
def cycle2685_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2685_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2685_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,27]⟩
def cycle2685_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2685 : PartitionData E W := ⟨6,![cycle2685_0,cycle2685_1,cycle2685_2,cycle2685_3,cycle2685_4,cycle2685_5]⟩
lemma valid_data2685 : data2685.Valid src2685 dst2685 Finset.univ := by decide +kernel

def src2686 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst2686 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle2686_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,27,14]⟩
def cycle2686_1 : CycleData E W := ⟨1,![1,15,7],![3,6,16]⟩
def cycle2686_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle2686_3 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2686_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2686_5 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2686_6 : CycleData E W := ⟨2,![17,22,13,18],![26,38,28,27]⟩
def data2686 : PartitionData E W := ⟨7,![cycle2686_0,cycle2686_1,cycle2686_2,cycle2686_3,cycle2686_4,cycle2686_5,cycle2686_6]⟩
lemma valid_data2686 : data2686.Valid src2686 dst2686 Finset.univ := by decide +kernel

def src2687 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst2687 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle2687_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2687_1 : CycleData E W := ⟨3,![2,10,17,16,7],![3,4,26,38,16]⟩
def cycle2687_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2687_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2687_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,27]⟩
def cycle2687_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2687 : PartitionData E W := ⟨6,![cycle2687_0,cycle2687_1,cycle2687_2,cycle2687_3,cycle2687_4,cycle2687_5]⟩
lemma valid_data2687 : data2687.Valid src2687 dst2687 Finset.univ := by decide +kernel

def src2688 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2688 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2688_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2688_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2688_2 : CycleData E W := ⟨3,![4,3,14,21,9],![2,8,4,28,18]⟩
def cycle2688_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2688_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2688_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2688 : PartitionData E W := ⟨6,![cycle2688_0,cycle2688_1,cycle2688_2,cycle2688_3,cycle2688_4,cycle2688_5]⟩
lemma valid_data2688 : data2688.Valid src2688 dst2688 Finset.univ := by decide +kernel

def src2689 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2689 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2689_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2689_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2689_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2689_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2689_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2689_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2689_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2689 : PartitionData E W := ⟨7,![cycle2689_0,cycle2689_1,cycle2689_2,cycle2689_3,cycle2689_4,cycle2689_5,cycle2689_6]⟩
lemma valid_data2689 : data2689.Valid src2689 dst2689 Finset.univ := by decide +kernel

def src2690 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2690 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2690_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2690_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2690_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2690_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,18]⟩
def cycle2690_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2690_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2690 : PartitionData E W := ⟨6,![cycle2690_0,cycle2690_1,cycle2690_2,cycle2690_3,cycle2690_4,cycle2690_5]⟩
lemma valid_data2690 : data2690.Valid src2690 dst2690 Finset.univ := by decide +kernel

def src2691 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2691 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2691_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2691_1 : CycleData E W := ⟨3,![2,10,16,17,7],![3,4,26,38,16]⟩
def cycle2691_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2691_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2691_4 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2691_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2691 : PartitionData E W := ⟨6,![cycle2691_0,cycle2691_1,cycle2691_2,cycle2691_3,cycle2691_4,cycle2691_5]⟩
lemma valid_data2691 : data2691.Valid src2691 dst2691 Finset.univ := by decide +kernel

def src2692 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2692 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2692_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2692_1 : CycleData E W := ⟨3,![2,10,16,17,7],![3,4,26,38,16]⟩
def cycle2692_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2692_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2692_4 : CycleData E W := ⟨3,![8,21,22,13,18],![16,18,38,28,27]⟩
def cycle2692_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2692 : PartitionData E W := ⟨6,![cycle2692_0,cycle2692_1,cycle2692_2,cycle2692_3,cycle2692_4,cycle2692_5]⟩
lemma valid_data2692 : data2692.Valid src2692 dst2692 Finset.univ := by decide +kernel

def src2693 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2693 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2693_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2693_1 : CycleData E W := ⟨3,![2,10,16,17,7],![3,4,26,38,16]⟩
def cycle2693_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2693_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2693_4 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2693_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2693 : PartitionData E W := ⟨6,![cycle2693_0,cycle2693_1,cycle2693_2,cycle2693_3,cycle2693_4,cycle2693_5]⟩
lemma valid_data2693 : data2693.Valid src2693 dst2693 Finset.univ := by decide +kernel

def src2694 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2694 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2694_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2694_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2694_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2694_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2694_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2694_5 : CycleData E W := ⟨3,![15,12,11,18,19],![6,27,14,26,38]⟩
def data2694 : PartitionData E W := ⟨6,![cycle2694_0,cycle2694_1,cycle2694_2,cycle2694_3,cycle2694_4,cycle2694_5]⟩
lemma valid_data2694 : data2694.Valid src2694 dst2694 Finset.univ := by decide +kernel

def src2695 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2695 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2695_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2695_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,26,14,27,16]⟩
def cycle2695_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2695_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2695_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2695_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2695 : PartitionData E W := ⟨6,![cycle2695_0,cycle2695_1,cycle2695_2,cycle2695_3,cycle2695_4,cycle2695_5]⟩
lemma valid_data2695 : data2695.Valid src2695 dst2695 Finset.univ := by decide +kernel

def src2696 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2696 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2696_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2696_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2696_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2696_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2696_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2696_5 : CycleData E W := ⟨3,![15,12,11,18,19],![6,27,14,26,38]⟩
def data2696 : PartitionData E W := ⟨6,![cycle2696_0,cycle2696_1,cycle2696_2,cycle2696_3,cycle2696_4,cycle2696_5]⟩
lemma valid_data2696 : data2696.Valid src2696 dst2696 Finset.univ := by decide +kernel

def src2697 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst2697 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle2697_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2697_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2697_2 : CycleData E W := ⟨3,![4,3,14,21,9],![2,8,4,28,18]⟩
def cycle2697_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle2697_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2697_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2697 : PartitionData E W := ⟨6,![cycle2697_0,cycle2697_1,cycle2697_2,cycle2697_3,cycle2697_4,cycle2697_5]⟩
lemma valid_data2697 : data2697.Valid src2697 dst2697 Finset.univ := by decide +kernel

def src2698 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst2698 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle2698_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2698_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2698_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2698_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2698_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2698_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2698_6 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2698 : PartitionData E W := ⟨7,![cycle2698_0,cycle2698_1,cycle2698_2,cycle2698_3,cycle2698_4,cycle2698_5,cycle2698_6]⟩
lemma valid_data2698 : data2698.Valid src2698 dst2698 Finset.univ := by decide +kernel

def src2699 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst2699 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle2699_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2699_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2699_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2699_3 : CycleData E W := ⟨3,![4,23,18,8,9],![2,8,38,16,18]⟩
def cycle2699_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2699_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2699 : PartitionData E W := ⟨6,![cycle2699_0,cycle2699_1,cycle2699_2,cycle2699_3,cycle2699_4,cycle2699_5]⟩
lemma valid_data2699 : data2699.Valid src2699 dst2699 Finset.univ := by decide +kernel

def src2700 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst2700 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle2700_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2700_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2700_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2700_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2700_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,27]⟩
def cycle2700_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2700 : PartitionData E W := ⟨6,![cycle2700_0,cycle2700_1,cycle2700_2,cycle2700_3,cycle2700_4,cycle2700_5]⟩
lemma valid_data2700 : data2700.Valid src2700 dst2700 Finset.univ := by decide +kernel

def src2701 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst2701 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle2701_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2701_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2701_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle2701_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2701_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,27]⟩
def cycle2701_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2701 : PartitionData E W := ⟨6,![cycle2701_0,cycle2701_1,cycle2701_2,cycle2701_3,cycle2701_4,cycle2701_5]⟩
lemma valid_data2701 : data2701.Valid src2701 dst2701 Finset.univ := by decide +kernel

def src2702 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst2702 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle2702_0 : CycleData E W := ⟨2,![0,15,8,9],![2,6,16,18]⟩
def cycle2702_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2702_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle2702_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2702_4 : CycleData E W := ⟨2,![6,11,16,7],![3,14,26,16]⟩
def cycle2702_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2702 : PartitionData E W := ⟨6,![cycle2702_0,cycle2702_1,cycle2702_2,cycle2702_3,cycle2702_4,cycle2702_5]⟩
lemma valid_data2702 : data2702.Valid src2702 dst2702 Finset.univ := by decide +kernel

def src2703 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst2703 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle2703_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2703_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2703_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2703_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2703_4 : CycleData E W := ⟨3,![15,8,21,22,19],![6,16,18,28,38]⟩
def cycle2703_5 : CycleData E W := ⟨2,![11,17,13,12],![14,26,27,28]⟩
def data2703 : PartitionData E W := ⟨6,![cycle2703_0,cycle2703_1,cycle2703_2,cycle2703_3,cycle2703_4,cycle2703_5]⟩
lemma valid_data2703 : data2703.Valid src2703 dst2703 Finset.univ := by decide +kernel

def src2704 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst2704 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle2704_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2704_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2704_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,14,26]⟩
def cycle2704_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2704_4 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2704_5 : CycleData E W := ⟨2,![17,13,22,18],![26,27,28,38]⟩
def data2704 : PartitionData E W := ⟨6,![cycle2704_0,cycle2704_1,cycle2704_2,cycle2704_3,cycle2704_4,cycle2704_5]⟩
lemma valid_data2704 : data2704.Valid src2704 dst2704 Finset.univ := by decide +kernel

def src2705 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst2705 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle2705_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2705_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2705_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2705_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2705_4 : CycleData E W := ⟨2,![15,8,22,19],![6,16,18,38]⟩
def cycle2705_5 : CycleData E W := ⟨2,![11,17,13,12],![14,26,27,28]⟩
def data2705 : PartitionData E W := ⟨6,![cycle2705_0,cycle2705_1,cycle2705_2,cycle2705_3,cycle2705_4,cycle2705_5]⟩
lemma valid_data2705 : data2705.Valid src2705 dst2705 Finset.univ := by decide +kernel

def src2706 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst2706 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle2706_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2706_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2706_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2706_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2706_4 : CycleData E W := ⟨4,![15,8,21,12,11,19],![6,16,18,28,14,26]⟩
def cycle2706_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2706 : PartitionData E W := ⟨6,![cycle2706_0,cycle2706_1,cycle2706_2,cycle2706_3,cycle2706_4,cycle2706_5]⟩
lemma valid_data2706 : data2706.Valid src2706 dst2706 Finset.univ := by decide +kernel

def src2707 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst2707 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle2707_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2707_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2707_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,14,26]⟩
def cycle2707_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2707_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,26]⟩
def cycle2707_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2707 : PartitionData E W := ⟨6,![cycle2707_0,cycle2707_1,cycle2707_2,cycle2707_3,cycle2707_4,cycle2707_5]⟩
lemma valid_data2707 : data2707.Valid src2707 dst2707 Finset.univ := by decide +kernel

def src2708 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst2708 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle2708_0 : CycleData E W := ⟨2,![0,15,8,9],![2,6,16,18]⟩
def cycle2708_1 : CycleData E W := ⟨2,![1,19,11,6],![3,6,26,14]⟩
def cycle2708_2 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2708_3 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2708_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2708_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,27,38]⟩
def data2708 : PartitionData E W := ⟨6,![cycle2708_0,cycle2708_1,cycle2708_2,cycle2708_3,cycle2708_4,cycle2708_5]⟩
lemma valid_data2708 : data2708.Valid src2708 dst2708 Finset.univ := by decide +kernel

def src2709 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst2709 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle2709_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2709_1 : CycleData E W := ⟨3,![2,14,19,15,7],![3,4,27,6,16]⟩
def cycle2709_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle2709_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2709_4 : CycleData E W := ⟨2,![8,21,22,16],![16,18,28,38]⟩
def cycle2709_5 : CycleData E W := ⟨2,![11,18,13,12],![14,26,27,28]⟩
def data2709 : PartitionData E W := ⟨6,![cycle2709_0,cycle2709_1,cycle2709_2,cycle2709_3,cycle2709_4,cycle2709_5]⟩
lemma valid_data2709 : data2709.Valid src2709 dst2709 Finset.univ := by decide +kernel

def src2710 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst2710 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle2710_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2710_1 : CycleData E W := ⟨3,![2,14,19,15,7],![3,4,27,6,16]⟩
def cycle2710_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,14,26]⟩
def cycle2710_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2710_4 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2710_5 : CycleData E W := ⟨2,![17,22,13,18],![26,38,28,27]⟩
def data2710 : PartitionData E W := ⟨6,![cycle2710_0,cycle2710_1,cycle2710_2,cycle2710_3,cycle2710_4,cycle2710_5]⟩
lemma valid_data2710 : data2710.Valid src2710 dst2710 Finset.univ := by decide +kernel

def src2711 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst2711 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle2711_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2711_1 : CycleData E W := ⟨3,![2,14,19,15,7],![3,4,27,6,16]⟩
def cycle2711_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle2711_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2711_4 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2711_5 : CycleData E W := ⟨2,![11,18,13,12],![14,26,27,28]⟩
def data2711 : PartitionData E W := ⟨6,![cycle2711_0,cycle2711_1,cycle2711_2,cycle2711_3,cycle2711_4,cycle2711_5]⟩
lemma valid_data2711 : data2711.Valid src2711 dst2711 Finset.univ := by decide +kernel

def src2712 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2712 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2712_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2712_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2712_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2712_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2712_4 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def cycle2712_5 : CycleData E W := ⟨3,![15,11,12,22,19],![6,26,14,28,38]⟩
def data2712 : PartitionData E W := ⟨6,![cycle2712_0,cycle2712_1,cycle2712_2,cycle2712_3,cycle2712_4,cycle2712_5]⟩
lemma valid_data2712 : data2712.Valid src2712 dst2712 Finset.univ := by decide +kernel

def src2713 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2713 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2713_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2713_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2713_2 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle2713_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2713_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2713_5 : CycleData E W := ⟨3,![15,11,12,22,19],![6,26,14,28,38]⟩
def data2713 : PartitionData E W := ⟨6,![cycle2713_0,cycle2713_1,cycle2713_2,cycle2713_3,cycle2713_4,cycle2713_5]⟩
lemma valid_data2713 : data2713.Valid src2713 dst2713 Finset.univ := by decide +kernel

def src2714 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2714 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2714_0 : CycleData E W := ⟨2,![0,19,22,9],![2,6,38,18]⟩
def cycle2714_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle2714_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2714_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2714_4 : CycleData E W := ⟨2,![6,11,16,7],![3,14,26,16]⟩
def cycle2714_5 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def data2714 : PartitionData E W := ⟨6,![cycle2714_0,cycle2714_1,cycle2714_2,cycle2714_3,cycle2714_4,cycle2714_5]⟩
lemma valid_data2714 : data2714.Valid src2714 dst2714 Finset.univ := by decide +kernel

def src2715 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst2715 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle2715_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2715_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2715_2 : CycleData E W := ⟨3,![3,23,19,15,10],![4,8,38,6,26]⟩
def cycle2715_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2715_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle2715_5 : CycleData E W := ⟨2,![11,16,13,12],![14,26,27,28]⟩
def data2715 : PartitionData E W := ⟨6,![cycle2715_0,cycle2715_1,cycle2715_2,cycle2715_3,cycle2715_4,cycle2715_5]⟩
lemma valid_data2715 : data2715.Valid src2715 dst2715 Finset.univ := by decide +kernel

def src2716 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst2716 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle2716_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2716_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2716_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,14,26]⟩
def cycle2716_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2716_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2716_5 : CycleData E W := ⟨3,![15,16,13,22,19],![6,26,27,28,38]⟩
def data2716 : PartitionData E W := ⟨6,![cycle2716_0,cycle2716_1,cycle2716_2,cycle2716_3,cycle2716_4,cycle2716_5]⟩
lemma valid_data2716 : data2716.Valid src2716 dst2716 Finset.univ := by decide +kernel

def src2717 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst2717 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle2717_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2717_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2717_2 : CycleData E W := ⟨3,![3,23,19,15,10],![4,8,38,6,26]⟩
def cycle2717_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2717_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle2717_5 : CycleData E W := ⟨2,![11,16,13,12],![14,26,27,28]⟩
def data2717 : PartitionData E W := ⟨6,![cycle2717_0,cycle2717_1,cycle2717_2,cycle2717_3,cycle2717_4,cycle2717_5]⟩
lemma valid_data2717 : data2717.Valid src2717 dst2717 Finset.univ := by decide +kernel

def src2718 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2718 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2718_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2718_1 : CycleData E W := ⟨2,![2,14,18,7],![3,4,27,16]⟩
def cycle2718_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2718_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2718_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2718_5 : CycleData E W := ⟨3,![15,11,12,13,19],![6,26,14,28,27]⟩
def data2718 : PartitionData E W := ⟨6,![cycle2718_0,cycle2718_1,cycle2718_2,cycle2718_3,cycle2718_4,cycle2718_5]⟩
lemma valid_data2718 : data2718.Valid src2718 dst2718 Finset.univ := by decide +kernel

def src2719 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2719 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2719_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2719_1 : CycleData E W := ⟨2,![2,14,18,7],![3,4,27,16]⟩
def cycle2719_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,14,26]⟩
def cycle2719_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2719_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2719_5 : CycleData E W := ⟨3,![15,16,22,13,19],![6,26,38,28,27]⟩
def data2719 : PartitionData E W := ⟨6,![cycle2719_0,cycle2719_1,cycle2719_2,cycle2719_3,cycle2719_4,cycle2719_5]⟩
lemma valid_data2719 : data2719.Valid src2719 dst2719 Finset.univ := by decide +kernel

def src2720 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2720 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2720_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2720_1 : CycleData E W := ⟨2,![2,14,18,7],![3,4,27,16]⟩
def cycle2720_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2720_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2720_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2720_5 : CycleData E W := ⟨3,![15,11,12,13,19],![6,26,14,28,27]⟩
def data2720 : PartitionData E W := ⟨6,![cycle2720_0,cycle2720_1,cycle2720_2,cycle2720_3,cycle2720_4,cycle2720_5]⟩
lemma valid_data2720 : data2720.Valid src2720 dst2720 Finset.univ := by decide +kernel

def src2721 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2721 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2721_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2721_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2721_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2721_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2721_4 : CycleData E W := ⟨3,![11,17,8,21,12],![14,26,16,18,28]⟩
def cycle2721_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2721 : PartitionData E W := ⟨6,![cycle2721_0,cycle2721_1,cycle2721_2,cycle2721_3,cycle2721_4,cycle2721_5]⟩
lemma valid_data2721 : data2721.Valid src2721 dst2721 Finset.univ := by decide +kernel

def src2722 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2722 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2722_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2722_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2722_2 : CycleData E W := ⟨3,![3,23,12,11,10],![4,8,28,14,26]⟩
def cycle2722_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2722_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2722_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2722 : PartitionData E W := ⟨6,![cycle2722_0,cycle2722_1,cycle2722_2,cycle2722_3,cycle2722_4,cycle2722_5]⟩
lemma valid_data2722 : data2722.Valid src2722 dst2722 Finset.univ := by decide +kernel

def src2723 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2723 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2723_0 : CycleData E W := ⟨2,![0,19,22,9],![2,6,38,18]⟩
def cycle2723_1 : CycleData E W := ⟨2,![1,15,14,2],![3,6,27,4]⟩
def cycle2723_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2723_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2723_4 : CycleData E W := ⟨2,![6,11,17,7],![3,14,26,16]⟩
def cycle2723_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2723 : PartitionData E W := ⟨6,![cycle2723_0,cycle2723_1,cycle2723_2,cycle2723_3,cycle2723_4,cycle2723_5]⟩
lemma valid_data2723 : data2723.Valid src2723 dst2723 Finset.univ := by decide +kernel

def src2724 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst2724 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle2724_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2724_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2724_2 : CycleData E W := ⟨3,![4,3,14,21,9],![2,8,4,28,18]⟩
def cycle2724_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2724_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2724_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data2724 : PartitionData E W := ⟨6,![cycle2724_0,cycle2724_1,cycle2724_2,cycle2724_3,cycle2724_4,cycle2724_5]⟩
lemma valid_data2724 : data2724.Valid src2724 dst2724 Finset.univ := by decide +kernel

def src2725 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst2725 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle2725_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2725_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2725_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2725_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2725_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2725_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2725_6 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data2725 : PartitionData E W := ⟨7,![cycle2725_0,cycle2725_1,cycle2725_2,cycle2725_3,cycle2725_4,cycle2725_5,cycle2725_6]⟩
lemma valid_data2725 : data2725.Valid src2725 dst2725 Finset.univ := by decide +kernel

def src2726 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst2726 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle2726_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2726_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2726_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2726_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,18]⟩
def cycle2726_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2726_5 : CycleData E W := ⟨3,![12,18,22,21,13],![14,27,38,18,28]⟩
def data2726 : PartitionData E W := ⟨6,![cycle2726_0,cycle2726_1,cycle2726_2,cycle2726_3,cycle2726_4,cycle2726_5]⟩
lemma valid_data2726 : data2726.Valid src2726 dst2726 Finset.univ := by decide +kernel

def src2727 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst2727 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle2727_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2727_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2727_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2727_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2727_4 : CycleData E W := ⟨3,![12,16,8,21,13],![14,27,16,18,28]⟩
def cycle2727_5 : CycleData E W := ⟨2,![15,11,18,19],![6,27,26,38]⟩
def data2727 : PartitionData E W := ⟨6,![cycle2727_0,cycle2727_1,cycle2727_2,cycle2727_3,cycle2727_4,cycle2727_5]⟩
lemma valid_data2727 : data2727.Valid src2727 dst2727 Finset.univ := by decide +kernel

def src2728 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst2728 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle2728_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2728_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,26,27,16]⟩
def cycle2728_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2728_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2728_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2728_5 : CycleData E W := ⟨3,![15,12,13,22,19],![6,27,14,28,38]⟩
def data2728 : PartitionData E W := ⟨6,![cycle2728_0,cycle2728_1,cycle2728_2,cycle2728_3,cycle2728_4,cycle2728_5]⟩
lemma valid_data2728 : data2728.Valid src2728 dst2728 Finset.univ := by decide +kernel

def src2729 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst2729 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle2729_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2729_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2729_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2729_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2729_4 : CycleData E W := ⟨3,![12,16,8,21,13],![14,27,16,18,28]⟩
def cycle2729_5 : CycleData E W := ⟨2,![15,11,18,19],![6,27,26,38]⟩
def data2729 : PartitionData E W := ⟨6,![cycle2729_0,cycle2729_1,cycle2729_2,cycle2729_3,cycle2729_4,cycle2729_5]⟩
lemma valid_data2729 : data2729.Valid src2729 dst2729 Finset.univ := by decide +kernel

def src2730 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst2730 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle2730_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2730_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2730_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2730_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2730_4 : CycleData E W := ⟨3,![15,8,21,22,19],![6,16,18,28,38]⟩
def cycle2730_5 : CycleData E W := ⟨2,![12,11,17,13],![14,28,26,27]⟩
def data2730 : PartitionData E W := ⟨6,![cycle2730_0,cycle2730_1,cycle2730_2,cycle2730_3,cycle2730_4,cycle2730_5]⟩
lemma valid_data2730 : data2730.Valid src2730 dst2730 Finset.univ := by decide +kernel

def src2731 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst2731 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle2731_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2731_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2731_2 : CycleData E W := ⟨3,![3,23,12,13,14],![4,8,28,14,27]⟩
def cycle2731_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2731_4 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2731_5 : CycleData E W := ⟨2,![11,22,18,17],![26,28,38,27]⟩
def data2731 : PartitionData E W := ⟨6,![cycle2731_0,cycle2731_1,cycle2731_2,cycle2731_3,cycle2731_4,cycle2731_5]⟩
lemma valid_data2731 : data2731.Valid src2731 dst2731 Finset.univ := by decide +kernel

def src2732 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst2732 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle2732_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2732_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2732_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2732_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2732_4 : CycleData E W := ⟨2,![15,8,22,19],![6,16,18,38]⟩
def cycle2732_5 : CycleData E W := ⟨2,![12,11,17,13],![14,28,26,27]⟩
def data2732 : PartitionData E W := ⟨6,![cycle2732_0,cycle2732_1,cycle2732_2,cycle2732_3,cycle2732_4,cycle2732_5]⟩
lemma valid_data2732 : data2732.Valid src2732 dst2732 Finset.univ := by decide +kernel

def src2733 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst2733 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle2733_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2733_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2733_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2733_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2733_4 : CycleData E W := ⟨4,![15,8,21,12,13,19],![6,16,18,28,14,27]⟩
def cycle2733_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2733 : PartitionData E W := ⟨6,![cycle2733_0,cycle2733_1,cycle2733_2,cycle2733_3,cycle2733_4,cycle2733_5]⟩
lemma valid_data2733 : data2733.Valid src2733 dst2733 Finset.univ := by decide +kernel

def src2734 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst2734 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle2734_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2734_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2734_2 : CycleData E W := ⟨3,![3,23,12,13,14],![4,8,28,14,27]⟩
def cycle2734_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2734_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,27]⟩
def cycle2734_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2734 : PartitionData E W := ⟨6,![cycle2734_0,cycle2734_1,cycle2734_2,cycle2734_3,cycle2734_4,cycle2734_5]⟩
lemma valid_data2734 : data2734.Valid src2734 dst2734 Finset.univ := by decide +kernel

def src2735 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst2735 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle2735_0 : CycleData E W := ⟨2,![0,15,8,9],![2,6,16,18]⟩
def cycle2735_1 : CycleData E W := ⟨2,![1,19,13,6],![3,6,27,14]⟩
def cycle2735_2 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2735_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2735_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2735_5 : CycleData E W := ⟨2,![21,11,17,22],![18,28,26,38]⟩
def data2735 : PartitionData E W := ⟨6,![cycle2735_0,cycle2735_1,cycle2735_2,cycle2735_3,cycle2735_4,cycle2735_5]⟩
lemma valid_data2735 : data2735.Valid src2735 dst2735 Finset.univ := by decide +kernel

def src2736 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst2736 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle2736_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2736_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2736_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2736_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2736_4 : CycleData E W := ⟨3,![15,8,21,11,19],![6,16,18,28,26]⟩
def cycle2736_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2736 : PartitionData E W := ⟨6,![cycle2736_0,cycle2736_1,cycle2736_2,cycle2736_3,cycle2736_4,cycle2736_5]⟩
lemma valid_data2736 : data2736.Valid src2736 dst2736 Finset.univ := by decide +kernel

def src2737 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst2737 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle2737_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2737_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2737_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,26]⟩
def cycle2737_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2737_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,26]⟩
def cycle2737_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2737 : PartitionData E W := ⟨6,![cycle2737_0,cycle2737_1,cycle2737_2,cycle2737_3,cycle2737_4,cycle2737_5]⟩
lemma valid_data2737 : data2737.Valid src2737 dst2737 Finset.univ := by decide +kernel

def src2738 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst2738 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle2738_0 : CycleData E W := ⟨2,![0,15,8,9],![2,6,16,18]⟩
def cycle2738_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2738_2 : CycleData E W := ⟨2,![3,23,17,14],![4,8,38,27]⟩
def cycle2738_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2738_4 : CycleData E W := ⟨2,![6,13,16,7],![3,14,27,16]⟩
def cycle2738_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data2738 : PartitionData E W := ⟨6,![cycle2738_0,cycle2738_1,cycle2738_2,cycle2738_3,cycle2738_4,cycle2738_5]⟩
lemma valid_data2738 : data2738.Valid src2738 dst2738 Finset.univ := by decide +kernel

def src2739 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst2739 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle2739_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2739_1 : CycleData E W := ⟨3,![2,10,19,15,7],![3,4,26,6,16]⟩
def cycle2739_2 : CycleData E W := ⟨2,![3,23,17,14],![4,8,38,27]⟩
def cycle2739_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2739_4 : CycleData E W := ⟨2,![8,21,22,16],![16,18,28,38]⟩
def cycle2739_5 : CycleData E W := ⟨2,![12,11,18,13],![14,28,26,27]⟩
def data2739 : PartitionData E W := ⟨6,![cycle2739_0,cycle2739_1,cycle2739_2,cycle2739_3,cycle2739_4,cycle2739_5]⟩
lemma valid_data2739 : data2739.Valid src2739 dst2739 Finset.univ := by decide +kernel

def src2740 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst2740 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle2740_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2740_1 : CycleData E W := ⟨3,![2,10,19,15,7],![3,4,26,6,16]⟩
def cycle2740_2 : CycleData E W := ⟨3,![3,23,12,13,14],![4,8,28,14,27]⟩
def cycle2740_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2740_4 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2740_5 : CycleData E W := ⟨2,![11,22,17,18],![26,28,38,27]⟩
def data2740 : PartitionData E W := ⟨6,![cycle2740_0,cycle2740_1,cycle2740_2,cycle2740_3,cycle2740_4,cycle2740_5]⟩
lemma valid_data2740 : data2740.Valid src2740 dst2740 Finset.univ := by decide +kernel

def src2741 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst2741 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle2741_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2741_1 : CycleData E W := ⟨3,![2,10,19,15,7],![3,4,26,6,16]⟩
def cycle2741_2 : CycleData E W := ⟨2,![3,23,17,14],![4,8,38,27]⟩
def cycle2741_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2741_4 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2741_5 : CycleData E W := ⟨2,![12,11,18,13],![14,28,26,27]⟩
def data2741 : PartitionData E W := ⟨6,![cycle2741_0,cycle2741_1,cycle2741_2,cycle2741_3,cycle2741_4,cycle2741_5]⟩
lemma valid_data2741 : data2741.Valid src2741 dst2741 Finset.univ := by decide +kernel

def src2742 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2742 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2742_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2742_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2742_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2742_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2742_4 : CycleData E W := ⟨3,![12,21,8,17,13],![14,28,18,16,27]⟩
def cycle2742_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2742 : PartitionData E W := ⟨6,![cycle2742_0,cycle2742_1,cycle2742_2,cycle2742_3,cycle2742_4,cycle2742_5]⟩
lemma valid_data2742 : data2742.Valid src2742 dst2742 Finset.univ := by decide +kernel

def src2743 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2743 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2743_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2743_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2743_2 : CycleData E W := ⟨3,![3,23,12,13,14],![4,8,28,14,27]⟩
def cycle2743_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2743_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2743_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2743 : PartitionData E W := ⟨6,![cycle2743_0,cycle2743_1,cycle2743_2,cycle2743_3,cycle2743_4,cycle2743_5]⟩
lemma valid_data2743 : data2743.Valid src2743 dst2743 Finset.univ := by decide +kernel

def src2744 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2744 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2744_0 : CycleData E W := ⟨2,![0,19,22,9],![2,6,38,18]⟩
def cycle2744_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle2744_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2744_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2744_4 : CycleData E W := ⟨2,![6,13,17,7],![3,14,27,16]⟩
def cycle2744_5 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def data2744 : PartitionData E W := ⟨6,![cycle2744_0,cycle2744_1,cycle2744_2,cycle2744_3,cycle2744_4,cycle2744_5]⟩
lemma valid_data2744 : data2744.Valid src2744 dst2744 Finset.univ := by decide +kernel

def src2745 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2745 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2745_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2745_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2745_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2745_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2745_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2745_5 : CycleData E W := ⟨3,![15,11,12,13,19],![6,26,28,14,27]⟩
def data2745 : PartitionData E W := ⟨6,![cycle2745_0,cycle2745_1,cycle2745_2,cycle2745_3,cycle2745_4,cycle2745_5]⟩
lemma valid_data2745 : data2745.Valid src2745 dst2745 Finset.univ := by decide +kernel

def src2746 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2746 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2746_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2746_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2746_2 : CycleData E W := ⟨3,![3,23,12,13,14],![4,8,28,14,27]⟩
def cycle2746_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2746_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2746_5 : CycleData E W := ⟨3,![15,11,22,18,19],![6,26,28,38,27]⟩
def data2746 : PartitionData E W := ⟨6,![cycle2746_0,cycle2746_1,cycle2746_2,cycle2746_3,cycle2746_4,cycle2746_5]⟩
lemma valid_data2746 : data2746.Valid src2746 dst2746 Finset.univ := by decide +kernel

def src2747 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2747 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2747_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2747_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2747_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2747_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2747_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2747_5 : CycleData E W := ⟨3,![15,11,12,13,19],![6,26,28,14,27]⟩
def data2747 : PartitionData E W := ⟨6,![cycle2747_0,cycle2747_1,cycle2747_2,cycle2747_3,cycle2747_4,cycle2747_5]⟩
lemma valid_data2747 : data2747.Valid src2747 dst2747 Finset.univ := by decide +kernel

def src2748 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2748 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2748_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2748_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2748_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2748_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2748_4 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def cycle2748_5 : CycleData E W := ⟨3,![15,13,12,22,19],![6,27,14,28,38]⟩
def data2748 : PartitionData E W := ⟨6,![cycle2748_0,cycle2748_1,cycle2748_2,cycle2748_3,cycle2748_4,cycle2748_5]⟩
lemma valid_data2748 : data2748.Valid src2748 dst2748 Finset.univ := by decide +kernel

def src2749 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2749 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2749_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2749_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2749_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,26]⟩
def cycle2749_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2749_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,26]⟩
def cycle2749_5 : CycleData E W := ⟨3,![15,13,12,22,19],![6,27,14,28,38]⟩
def data2749 : PartitionData E W := ⟨6,![cycle2749_0,cycle2749_1,cycle2749_2,cycle2749_3,cycle2749_4,cycle2749_5]⟩
lemma valid_data2749 : data2749.Valid src2749 dst2749 Finset.univ := by decide +kernel

def src2750 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2750 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2750_0 : CycleData E W := ⟨2,![0,19,22,9],![2,6,38,18]⟩
def cycle2750_1 : CycleData E W := ⟨2,![1,15,13,6],![3,6,27,14]⟩
def cycle2750_2 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2750_3 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2750_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2750_5 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def data2750 : PartitionData E W := ⟨6,![cycle2750_0,cycle2750_1,cycle2750_2,cycle2750_3,cycle2750_4,cycle2750_5]⟩
lemma valid_data2750 : data2750.Valid src2750 dst2750 Finset.univ := by decide +kernel

def src2751 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst2751 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle2751_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2751_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2751_2 : CycleData E W := ⟨3,![3,23,19,15,14],![4,8,38,6,27]⟩
def cycle2751_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2751_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle2751_5 : CycleData E W := ⟨2,![12,11,16,13],![14,28,26,27]⟩
def data2751 : PartitionData E W := ⟨6,![cycle2751_0,cycle2751_1,cycle2751_2,cycle2751_3,cycle2751_4,cycle2751_5]⟩
lemma valid_data2751 : data2751.Valid src2751 dst2751 Finset.univ := by decide +kernel

def src2752 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst2752 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle2752_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2752_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2752_2 : CycleData E W := ⟨3,![3,23,12,13,14],![4,8,28,14,27]⟩
def cycle2752_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2752_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2752_5 : CycleData E W := ⟨3,![15,16,11,22,19],![6,27,26,28,38]⟩
def data2752 : PartitionData E W := ⟨6,![cycle2752_0,cycle2752_1,cycle2752_2,cycle2752_3,cycle2752_4,cycle2752_5]⟩
lemma valid_data2752 : data2752.Valid src2752 dst2752 Finset.univ := by decide +kernel

def src2753 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst2753 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle2753_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2753_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2753_2 : CycleData E W := ⟨3,![3,23,19,15,14],![4,8,38,6,27]⟩
def cycle2753_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2753_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle2753_5 : CycleData E W := ⟨2,![12,11,16,13],![14,28,26,27]⟩
def data2753 : PartitionData E W := ⟨6,![cycle2753_0,cycle2753_1,cycle2753_2,cycle2753_3,cycle2753_4,cycle2753_5]⟩
lemma valid_data2753 : data2753.Valid src2753 dst2753 Finset.univ := by decide +kernel

def src2754 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst2754 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle2754_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2754_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,26,16]⟩
def cycle2754_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2754_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2754_4 : CycleData E W := ⟨3,![15,8,21,22,19],![6,16,18,28,38]⟩
def cycle2754_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2754 : PartitionData E W := ⟨6,![cycle2754_0,cycle2754_1,cycle2754_2,cycle2754_3,cycle2754_4,cycle2754_5]⟩
lemma valid_data2754 : data2754.Valid src2754 dst2754 Finset.univ := by decide +kernel

def src2755 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst2755 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle2755_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2755_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,27,14,26,16]⟩
def cycle2755_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2755_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2755_4 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2755_5 : CycleData E W := ⟨2,![13,22,18,17],![26,28,38,27]⟩
def data2755 : PartitionData E W := ⟨6,![cycle2755_0,cycle2755_1,cycle2755_2,cycle2755_3,cycle2755_4,cycle2755_5]⟩
lemma valid_data2755 : data2755.Valid src2755 dst2755 Finset.univ := by decide +kernel

def src2756 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst2756 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle2756_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2756_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,26,16]⟩
def cycle2756_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2756_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2756_4 : CycleData E W := ⟨2,![15,8,22,19],![6,16,18,38]⟩
def cycle2756_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2756 : PartitionData E W := ⟨6,![cycle2756_0,cycle2756_1,cycle2756_2,cycle2756_3,cycle2756_4,cycle2756_5]⟩
lemma valid_data2756 : data2756.Valid src2756 dst2756 Finset.univ := by decide +kernel

def src2757 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst2757 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle2757_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2757_1 : CycleData E W := ⟨3,![2,10,19,15,7],![3,4,27,6,16]⟩
def cycle2757_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2757_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2757_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2757_5 : CycleData E W := ⟨2,![11,18,17,12],![14,27,38,26]⟩
def data2757 : PartitionData E W := ⟨6,![cycle2757_0,cycle2757_1,cycle2757_2,cycle2757_3,cycle2757_4,cycle2757_5]⟩
lemma valid_data2757 : data2757.Valid src2757 dst2757 Finset.univ := by decide +kernel

def src2758 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst2758 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle2758_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2758_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,27,14,26,16]⟩
def cycle2758_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2758_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2758_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,27]⟩
def cycle2758_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2758 : PartitionData E W := ⟨6,![cycle2758_0,cycle2758_1,cycle2758_2,cycle2758_3,cycle2758_4,cycle2758_5]⟩
lemma valid_data2758 : data2758.Valid src2758 dst2758 Finset.univ := by decide +kernel

def src2759 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst2759 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle2759_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2759_1 : CycleData E W := ⟨3,![2,10,19,15,7],![3,4,27,6,16]⟩
def cycle2759_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2759_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2759_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2759_5 : CycleData E W := ⟨2,![11,18,17,12],![14,27,38,26]⟩
def data2759 : PartitionData E W := ⟨6,![cycle2759_0,cycle2759_1,cycle2759_2,cycle2759_3,cycle2759_4,cycle2759_5]⟩
lemma valid_data2759 : data2759.Valid src2759 dst2759 Finset.univ := by decide +kernel

def src2760 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst2760 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle2760_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2760_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,27,16]⟩
def cycle2760_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2760_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2760_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,26]⟩
def cycle2760_5 : CycleData E W := ⟨2,![11,17,18,12],![14,27,38,26]⟩
def data2760 : PartitionData E W := ⟨6,![cycle2760_0,cycle2760_1,cycle2760_2,cycle2760_3,cycle2760_4,cycle2760_5]⟩
lemma valid_data2760 : data2760.Valid src2760 dst2760 Finset.univ := by decide +kernel

def src2761 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst2761 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle2761_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,26,14]⟩
def cycle2761_1 : CycleData E W := ⟨1,![1,15,7],![3,6,16]⟩
def cycle2761_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,27,14]⟩
def cycle2761_3 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2761_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2761_5 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle2761_6 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2761 : PartitionData E W := ⟨7,![cycle2761_0,cycle2761_1,cycle2761_2,cycle2761_3,cycle2761_4,cycle2761_5,cycle2761_6]⟩
lemma valid_data2761 : data2761.Valid src2761 dst2761 Finset.univ := by decide +kernel

def src2762 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst2762 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle2762_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2762_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,27,16]⟩
def cycle2762_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2762_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2762_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,26]⟩
def cycle2762_5 : CycleData E W := ⟨2,![11,17,18,12],![14,27,38,26]⟩
def data2762 : PartitionData E W := ⟨6,![cycle2762_0,cycle2762_1,cycle2762_2,cycle2762_3,cycle2762_4,cycle2762_5]⟩
lemma valid_data2762 : data2762.Valid src2762 dst2762 Finset.univ := by decide +kernel

def src2763 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst2763 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle2763_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2763_1 : CycleData E W := ⟨3,![2,10,17,16,7],![3,4,27,38,16]⟩
def cycle2763_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2763_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2763_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,26]⟩
def cycle2763_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2763 : PartitionData E W := ⟨6,![cycle2763_0,cycle2763_1,cycle2763_2,cycle2763_3,cycle2763_4,cycle2763_5]⟩
lemma valid_data2763 : data2763.Valid src2763 dst2763 Finset.univ := by decide +kernel

def src2764 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst2764 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle2764_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,26,14]⟩
def cycle2764_1 : CycleData E W := ⟨1,![1,15,7],![3,6,16]⟩
def cycle2764_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,27,14]⟩
def cycle2764_3 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2764_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2764_5 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2764_6 : CycleData E W := ⟨2,![13,22,17,18],![26,28,38,27]⟩
def data2764 : PartitionData E W := ⟨7,![cycle2764_0,cycle2764_1,cycle2764_2,cycle2764_3,cycle2764_4,cycle2764_5,cycle2764_6]⟩
lemma valid_data2764 : data2764.Valid src2764 dst2764 Finset.univ := by decide +kernel

def src2765 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst2765 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle2765_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2765_1 : CycleData E W := ⟨3,![2,10,17,16,7],![3,4,27,38,16]⟩
def cycle2765_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2765_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2765_4 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,26]⟩
def cycle2765_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2765 : PartitionData E W := ⟨6,![cycle2765_0,cycle2765_1,cycle2765_2,cycle2765_3,cycle2765_4,cycle2765_5]⟩
lemma valid_data2765 : data2765.Valid src2765 dst2765 Finset.univ := by decide +kernel

def src2766 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2766 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2766_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2766_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2766_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2766_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2766_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2766_5 : CycleData E W := ⟨3,![15,12,11,18,19],![6,26,14,27,38]⟩
def data2766 : PartitionData E W := ⟨6,![cycle2766_0,cycle2766_1,cycle2766_2,cycle2766_3,cycle2766_4,cycle2766_5]⟩
lemma valid_data2766 : data2766.Valid src2766 dst2766 Finset.univ := by decide +kernel

def src2767 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2767 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2767_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2767_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,27,14,26,16]⟩
def cycle2767_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2767_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2767_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2767_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2767 : PartitionData E W := ⟨6,![cycle2767_0,cycle2767_1,cycle2767_2,cycle2767_3,cycle2767_4,cycle2767_5]⟩
lemma valid_data2767 : data2767.Valid src2767 dst2767 Finset.univ := by decide +kernel

def src2768 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2768 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2768_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2768_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2768_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2768_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2768_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2768_5 : CycleData E W := ⟨3,![15,12,11,18,19],![6,26,14,27,38]⟩
def data2768 : PartitionData E W := ⟨6,![cycle2768_0,cycle2768_1,cycle2768_2,cycle2768_3,cycle2768_4,cycle2768_5]⟩
lemma valid_data2768 : data2768.Valid src2768 dst2768 Finset.univ := by decide +kernel

def src2769 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2769 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2769_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2769_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,26,16]⟩
def cycle2769_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2769_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2769_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle2769_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2769 : PartitionData E W := ⟨6,![cycle2769_0,cycle2769_1,cycle2769_2,cycle2769_3,cycle2769_4,cycle2769_5]⟩
lemma valid_data2769 : data2769.Valid src2769 dst2769 Finset.univ := by decide +kernel

def src2770 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2770 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2770_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2770_1 : CycleData E W := ⟨4,![2,10,11,12,16,7],![3,4,27,14,26,16]⟩
def cycle2770_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2770_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2770_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2770_5 : CycleData E W := ⟨3,![15,13,22,18,19],![6,26,28,38,27]⟩
def data2770 : PartitionData E W := ⟨6,![cycle2770_0,cycle2770_1,cycle2770_2,cycle2770_3,cycle2770_4,cycle2770_5]⟩
lemma valid_data2770 : data2770.Valid src2770 dst2770 Finset.univ := by decide +kernel

def src2771 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2771 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2771_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2771_1 : CycleData E W := ⟨3,![2,14,13,16,7],![3,4,28,26,16]⟩
def cycle2771_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2771_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2771_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2771_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2771 : PartitionData E W := ⟨6,![cycle2771_0,cycle2771_1,cycle2771_2,cycle2771_3,cycle2771_4,cycle2771_5]⟩
lemma valid_data2771 : data2771.Valid src2771 dst2771 Finset.univ := by decide +kernel

def src2772 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst2772 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle2772_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2772_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2772_2 : CycleData E W := ⟨3,![4,3,14,21,9],![2,8,4,28,18]⟩
def cycle2772_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle2772_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2772_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2772 : PartitionData E W := ⟨6,![cycle2772_0,cycle2772_1,cycle2772_2,cycle2772_3,cycle2772_4,cycle2772_5]⟩
lemma valid_data2772 : data2772.Valid src2772 dst2772 Finset.univ := by decide +kernel

def src2773 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst2773 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle2773_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2773_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2773_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2773_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2773_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2773_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2773_6 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2773 : PartitionData E W := ⟨7,![cycle2773_0,cycle2773_1,cycle2773_2,cycle2773_3,cycle2773_4,cycle2773_5,cycle2773_6]⟩
lemma valid_data2773 : data2773.Valid src2773 dst2773 Finset.univ := by decide +kernel

def src2774 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst2774 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle2774_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2774_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2774_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2774_3 : CycleData E W := ⟨3,![4,23,18,8,9],![2,8,38,16,18]⟩
def cycle2774_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2774_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2774 : PartitionData E W := ⟨6,![cycle2774_0,cycle2774_1,cycle2774_2,cycle2774_3,cycle2774_4,cycle2774_5]⟩
lemma valid_data2774 : data2774.Valid src2774 dst2774 Finset.univ := by decide +kernel

def src2775 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2775 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2775_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2775_1 : CycleData E W := ⟨2,![2,10,18,7],![3,4,27,16]⟩
def cycle2775_2 : CycleData E W := ⟨3,![4,3,14,21,9],![2,8,4,28,18]⟩
def cycle2775_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2775_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2775_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2775 : PartitionData E W := ⟨6,![cycle2775_0,cycle2775_1,cycle2775_2,cycle2775_3,cycle2775_4,cycle2775_5]⟩
lemma valid_data2775 : data2775.Valid src2775 dst2775 Finset.univ := by decide +kernel

def src2776 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2776 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2776_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2776_1 : CycleData E W := ⟨2,![2,10,18,7],![3,4,27,16]⟩
def cycle2776_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2776_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2776_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2776_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2776_6 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2776 : PartitionData E W := ⟨7,![cycle2776_0,cycle2776_1,cycle2776_2,cycle2776_3,cycle2776_4,cycle2776_5,cycle2776_6]⟩
lemma valid_data2776 : data2776.Valid src2776 dst2776 Finset.univ := by decide +kernel

def src2777 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2777 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2777_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2777_1 : CycleData E W := ⟨2,![2,10,18,7],![3,4,27,16]⟩
def cycle2777_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2777_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,18]⟩
def cycle2777_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2777_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2777 : PartitionData E W := ⟨6,![cycle2777_0,cycle2777_1,cycle2777_2,cycle2777_3,cycle2777_4,cycle2777_5]⟩
lemma valid_data2777 : data2777.Valid src2777 dst2777 Finset.univ := by decide +kernel

def src2778 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst2778 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle2778_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2778_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2778_2 : CycleData E W := ⟨2,![3,23,22,14],![4,8,38,28]⟩
def cycle2778_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2778_4 : CycleData E W := ⟨3,![12,16,8,21,13],![14,26,16,18,28]⟩
def cycle2778_5 : CycleData E W := ⟨2,![15,11,18,19],![6,26,27,38]⟩
def data2778 : PartitionData E W := ⟨6,![cycle2778_0,cycle2778_1,cycle2778_2,cycle2778_3,cycle2778_4,cycle2778_5]⟩
lemma valid_data2778 : data2778.Valid src2778 dst2778 Finset.univ := by decide +kernel

def src2779 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst2779 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle2779_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2779_1 : CycleData E W := ⟨3,![2,10,11,16,7],![3,4,27,26,16]⟩
def cycle2779_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2779_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2779_4 : CycleData E W := ⟨2,![8,21,18,17],![16,18,38,27]⟩
def cycle2779_5 : CycleData E W := ⟨3,![15,12,13,22,19],![6,26,14,28,38]⟩
def data2779 : PartitionData E W := ⟨6,![cycle2779_0,cycle2779_1,cycle2779_2,cycle2779_3,cycle2779_4,cycle2779_5]⟩
lemma valid_data2779 : data2779.Valid src2779 dst2779 Finset.univ := by decide +kernel

def src2780 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst2780 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle2780_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2780_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2780_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2780_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2780_4 : CycleData E W := ⟨3,![12,16,8,21,13],![14,26,16,18,28]⟩
def cycle2780_5 : CycleData E W := ⟨2,![15,11,18,19],![6,26,27,38]⟩
def data2780 : PartitionData E W := ⟨6,![cycle2780_0,cycle2780_1,cycle2780_2,cycle2780_3,cycle2780_4,cycle2780_5]⟩
lemma valid_data2780 : data2780.Valid src2780 dst2780 Finset.univ := by decide +kernel

def src2781 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst2781 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle2781_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2781_1 : CycleData E W := ⟨2,![2,10,18,7],![3,4,27,16]⟩
def cycle2781_2 : CycleData E W := ⟨3,![4,3,14,21,9],![2,8,4,28,18]⟩
def cycle2781_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2781_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2781_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2781 : PartitionData E W := ⟨6,![cycle2781_0,cycle2781_1,cycle2781_2,cycle2781_3,cycle2781_4,cycle2781_5]⟩
lemma valid_data2781 : data2781.Valid src2781 dst2781 Finset.univ := by decide +kernel

def src2782 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst2782 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle2782_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2782_1 : CycleData E W := ⟨2,![2,10,18,7],![3,4,27,16]⟩
def cycle2782_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2782_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2782_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2782_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2782_6 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2782 : PartitionData E W := ⟨7,![cycle2782_0,cycle2782_1,cycle2782_2,cycle2782_3,cycle2782_4,cycle2782_5,cycle2782_6]⟩
lemma valid_data2782 : data2782.Valid src2782 dst2782 Finset.univ := by decide +kernel

def src2783 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst2783 : E → W := ![6,3,4,8,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle2783_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2783_1 : CycleData E W := ⟨2,![2,10,18,7],![3,4,27,16]⟩
def cycle2783_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2783_3 : CycleData E W := ⟨3,![4,23,17,8,9],![2,8,38,16,18]⟩
def cycle2783_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2783_5 : CycleData E W := ⟨3,![12,16,22,21,13],![14,26,38,18,28]⟩
def data2783 : PartitionData E W := ⟨6,![cycle2783_0,cycle2783_1,cycle2783_2,cycle2783_3,cycle2783_4,cycle2783_5]⟩
lemma valid_data2783 : data2783.Valid src2783 dst2783 Finset.univ := by decide +kernel

def src2784 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst2784 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2784_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2784_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2784_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2784_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2784_4 : CycleData E W := ⟨3,![10,11,16,22,14],![4,14,26,38,28]⟩
def cycle2784_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2784 : PartitionData E W := ⟨6,![cycle2784_0,cycle2784_1,cycle2784_2,cycle2784_3,cycle2784_4,cycle2784_5]⟩
lemma valid_data2784 : data2784.Valid src2784 dst2784 Finset.univ := by decide +kernel

def src2785 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst2785 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2785_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2785_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2785_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle2785_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2785_4 : CycleData E W := ⟨3,![10,11,16,22,14],![4,14,26,38,28]⟩
def cycle2785_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2785 : PartitionData E W := ⟨6,![cycle2785_0,cycle2785_1,cycle2785_2,cycle2785_3,cycle2785_4,cycle2785_5]⟩
lemma valid_data2785 : data2785.Valid src2785 dst2785 Finset.univ := by decide +kernel

def src2786 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst2786 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2786_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2786_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2786_2 : CycleData E W := ⟨3,![3,23,16,11,10],![4,8,38,26,14]⟩
def cycle2786_3 : CycleData E W := ⟨3,![4,20,13,18,9],![2,8,28,27,16]⟩
def cycle2786_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2786_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2786 : PartitionData E W := ⟨6,![cycle2786_0,cycle2786_1,cycle2786_2,cycle2786_3,cycle2786_4,cycle2786_5]⟩
lemma valid_data2786 : data2786.Valid src2786 dst2786 Finset.univ := by decide +kernel

def src2787 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst2787 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2787_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2787_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2787_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,26,14]⟩
def cycle2787_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2787_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2787_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2787 : PartitionData E W := ⟨6,![cycle2787_0,cycle2787_1,cycle2787_2,cycle2787_3,cycle2787_4,cycle2787_5]⟩
lemma valid_data2787 : data2787.Valid src2787 dst2787 Finset.univ := by decide +kernel

def src2788 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst2788 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2788_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2788_1 : CycleData E W := ⟨4,![2,10,11,18,21,7],![3,4,14,26,38,18]⟩
def cycle2788_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2788_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2788_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2788_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2788 : PartitionData E W := ⟨6,![cycle2788_0,cycle2788_1,cycle2788_2,cycle2788_3,cycle2788_4,cycle2788_5]⟩
lemma valid_data2788 : data2788.Valid src2788 dst2788 Finset.univ := by decide +kernel

def src2789 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst2789 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2789_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,6,3,18,16]⟩
def cycle2789_1 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2789_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2789_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle2789_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2789_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2789 : PartitionData E W := ⟨6,![cycle2789_0,cycle2789_1,cycle2789_2,cycle2789_3,cycle2789_4,cycle2789_5]⟩
lemma valid_data2789 : data2789.Valid src2789 dst2789 Finset.univ := by decide +kernel

def src2790 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst2790 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2790_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2790_1 : CycleData E W := ⟨3,![1,19,22,21,7],![3,6,38,28,18]⟩
def cycle2790_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2790_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2790_4 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2790_5 : CycleData E W := ⟨2,![16,12,13,17],![16,26,28,27]⟩
def data2790 : PartitionData E W := ⟨6,![cycle2790_0,cycle2790_1,cycle2790_2,cycle2790_3,cycle2790_4,cycle2790_5]⟩
lemma valid_data2790 : data2790.Valid src2790 dst2790 Finset.univ := by decide +kernel

def src2791 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst2791 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2791_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2791_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2791_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2791_3 : CycleData E W := ⟨3,![4,3,14,17,9],![2,8,4,27,16]⟩
def cycle2791_4 : CycleData E W := ⟨3,![20,8,16,12,23],![8,18,16,26,28]⟩
def cycle2791_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2791 : PartitionData E W := ⟨6,![cycle2791_0,cycle2791_1,cycle2791_2,cycle2791_3,cycle2791_4,cycle2791_5]⟩
lemma valid_data2791 : data2791.Valid src2791 dst2791 Finset.univ := by decide +kernel

def src2792 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst2792 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2792_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2792_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2792_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2792_3 : CycleData E W := ⟨3,![4,3,14,17,9],![2,8,4,27,16]⟩
def cycle2792_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle2792_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2792 : PartitionData E W := ⟨6,![cycle2792_0,cycle2792_1,cycle2792_2,cycle2792_3,cycle2792_4,cycle2792_5]⟩
lemma valid_data2792 : data2792.Valid src2792 dst2792 Finset.univ := by decide +kernel

def src2793 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst2793 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle2793_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2793_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2793_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2793_3 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle2793_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle2793_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2793 : PartitionData E W := ⟨6,![cycle2793_0,cycle2793_1,cycle2793_2,cycle2793_3,cycle2793_4,cycle2793_5]⟩
lemma valid_data2793 : data2793.Valid src2793 dst2793 Finset.univ := by decide +kernel

def src2794 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst2794 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle2794_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2794_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2794_2 : CycleData E W := ⟨3,![4,23,12,16,9],![2,8,28,26,16]⟩
def cycle2794_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2794_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle2794_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2794 : PartitionData E W := ⟨6,![cycle2794_0,cycle2794_1,cycle2794_2,cycle2794_3,cycle2794_4,cycle2794_5]⟩
lemma valid_data2794 : data2794.Valid src2794 dst2794 Finset.univ := by decide +kernel

def src2795 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst2795 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle2795_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2795_1 : CycleData E W := ⟨3,![1,19,13,21,7],![3,6,27,28,18]⟩
def cycle2795_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2795_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2795_4 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,26,16]⟩
def cycle2795_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2795 : PartitionData E W := ⟨6,![cycle2795_0,cycle2795_1,cycle2795_2,cycle2795_3,cycle2795_4,cycle2795_5]⟩
lemma valid_data2795 : data2795.Valid src2795 dst2795 Finset.univ := by decide +kernel

def src2796 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst2796 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2796_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2796_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2796_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2796_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2796_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle2796_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2796 : PartitionData E W := ⟨6,![cycle2796_0,cycle2796_1,cycle2796_2,cycle2796_3,cycle2796_4,cycle2796_5]⟩
lemma valid_data2796 : data2796.Valid src2796 dst2796 Finset.univ := by decide +kernel

def src2797 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst2797 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2797_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2797_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2797_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle2797_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2797_4 : CycleData E W := ⟨3,![10,11,15,19,14],![4,14,26,6,27]⟩
def cycle2797_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2797 : PartitionData E W := ⟨6,![cycle2797_0,cycle2797_1,cycle2797_2,cycle2797_3,cycle2797_4,cycle2797_5]⟩
lemma valid_data2797 : data2797.Valid src2797 dst2797 Finset.univ := by decide +kernel

def src2798 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst2798 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2798_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2798_1 : CycleData E W := ⟨3,![1,19,18,8,7],![3,6,27,16,18]⟩
def cycle2798_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2798_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle2798_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2798_5 : CycleData E W := ⟨2,![21,12,16,22],![18,28,26,38]⟩
def data2798 : PartitionData E W := ⟨6,![cycle2798_0,cycle2798_1,cycle2798_2,cycle2798_3,cycle2798_4,cycle2798_5]⟩
lemma valid_data2798 : data2798.Valid src2798 dst2798 Finset.univ := by decide +kernel

def src2799 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst2799 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2799_0 : CycleData E W := ⟨3,![0,15,14,3,4],![2,6,27,4,8]⟩
def cycle2799_1 : CycleData E W := ⟨3,![1,19,23,20,7],![3,6,38,8,18]⟩
def cycle2799_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2799_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,26,16]⟩
def cycle2799_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2799_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2799 : PartitionData E W := ⟨6,![cycle2799_0,cycle2799_1,cycle2799_2,cycle2799_3,cycle2799_4,cycle2799_5]⟩
lemma valid_data2799 : data2799.Valid src2799 dst2799 Finset.univ := by decide +kernel

def lookupB13 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data2600 else (if j < 2 then data2601 else data2602)) else (if j < 4 then data2603 else (if j < 5 then data2604 else data2605))) else (if j < 9 then (if j < 7 then data2606 else (if j < 8 then data2607 else data2608)) else (if j < 10 then data2609 else (if j < 11 then data2610 else data2611)))) else (if j < 18 then (if j < 15 then (if j < 13 then data2612 else (if j < 14 then data2613 else data2614)) else (if j < 16 then data2615 else (if j < 17 then data2616 else data2617))) else (if j < 21 then (if j < 19 then data2618 else (if j < 20 then data2619 else data2620)) else (if j < 23 then (if j < 22 then data2621 else data2622) else (if j < 24 then data2623 else data2624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data2625 else (if j < 27 then data2626 else data2627)) else (if j < 29 then data2628 else (if j < 30 then data2629 else data2630))) else (if j < 34 then (if j < 32 then data2631 else (if j < 33 then data2632 else data2633)) else (if j < 35 then data2634 else (if j < 36 then data2635 else data2636)))) else (if j < 43 then (if j < 40 then (if j < 38 then data2637 else (if j < 39 then data2638 else data2639)) else (if j < 41 then data2640 else (if j < 42 then data2641 else data2642))) else (if j < 46 then (if j < 44 then data2643 else (if j < 45 then data2644 else data2645)) else (if j < 48 then (if j < 47 then data2646 else data2647) else (if j < 49 then data2648 else data2649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data2650 else (if j < 52 then data2651 else data2652)) else (if j < 54 then data2653 else (if j < 55 then data2654 else data2655))) else (if j < 59 then (if j < 57 then data2656 else (if j < 58 then data2657 else data2658)) else (if j < 60 then data2659 else (if j < 61 then data2660 else data2661)))) else (if j < 68 then (if j < 65 then (if j < 63 then data2662 else (if j < 64 then data2663 else data2664)) else (if j < 66 then data2665 else (if j < 67 then data2666 else data2667))) else (if j < 71 then (if j < 69 then data2668 else (if j < 70 then data2669 else data2670)) else (if j < 73 then (if j < 72 then data2671 else data2672) else (if j < 74 then data2673 else data2674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data2675 else (if j < 77 then data2676 else data2677)) else (if j < 79 then data2678 else (if j < 80 then data2679 else data2680))) else (if j < 84 then (if j < 82 then data2681 else (if j < 83 then data2682 else data2683)) else (if j < 85 then data2684 else (if j < 86 then data2685 else data2686)))) else (if j < 93 then (if j < 90 then (if j < 88 then data2687 else (if j < 89 then data2688 else data2689)) else (if j < 91 then data2690 else (if j < 92 then data2691 else data2692))) else (if j < 96 then (if j < 94 then data2693 else (if j < 95 then data2694 else data2695)) else (if j < 98 then (if j < 97 then data2696 else data2697) else (if j < 99 then data2698 else data2699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data2700 else (if j < 102 then data2701 else data2702)) else (if j < 104 then data2703 else (if j < 105 then data2704 else data2705))) else (if j < 109 then (if j < 107 then data2706 else (if j < 108 then data2707 else data2708)) else (if j < 110 then data2709 else (if j < 111 then data2710 else data2711)))) else (if j < 118 then (if j < 115 then (if j < 113 then data2712 else (if j < 114 then data2713 else data2714)) else (if j < 116 then data2715 else (if j < 117 then data2716 else data2717))) else (if j < 121 then (if j < 119 then data2718 else (if j < 120 then data2719 else data2720)) else (if j < 123 then (if j < 122 then data2721 else data2722) else (if j < 124 then data2723 else data2724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data2725 else (if j < 127 then data2726 else data2727)) else (if j < 129 then data2728 else (if j < 130 then data2729 else data2730))) else (if j < 134 then (if j < 132 then data2731 else (if j < 133 then data2732 else data2733)) else (if j < 135 then data2734 else (if j < 136 then data2735 else data2736)))) else (if j < 143 then (if j < 140 then (if j < 138 then data2737 else (if j < 139 then data2738 else data2739)) else (if j < 141 then data2740 else (if j < 142 then data2741 else data2742))) else (if j < 146 then (if j < 144 then data2743 else (if j < 145 then data2744 else data2745)) else (if j < 148 then (if j < 147 then data2746 else data2747) else (if j < 149 then data2748 else data2749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data2750 else (if j < 152 then data2751 else data2752)) else (if j < 154 then data2753 else (if j < 155 then data2754 else data2755))) else (if j < 159 then (if j < 157 then data2756 else (if j < 158 then data2757 else data2758)) else (if j < 160 then data2759 else (if j < 161 then data2760 else data2761)))) else (if j < 168 then (if j < 165 then (if j < 163 then data2762 else (if j < 164 then data2763 else data2764)) else (if j < 166 then data2765 else (if j < 167 then data2766 else data2767))) else (if j < 171 then (if j < 169 then data2768 else (if j < 170 then data2769 else data2770)) else (if j < 173 then (if j < 172 then data2771 else data2772) else (if j < 174 then data2773 else data2774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data2775 else (if j < 177 then data2776 else data2777)) else (if j < 179 then data2778 else (if j < 180 then data2779 else data2780))) else (if j < 184 then (if j < 182 then data2781 else (if j < 183 then data2782 else data2783)) else (if j < 185 then data2784 else (if j < 186 then data2785 else data2786)))) else (if j < 193 then (if j < 190 then (if j < 188 then data2787 else (if j < 189 then data2788 else data2789)) else (if j < 191 then data2790 else (if j < 192 then data2791 else data2792))) else (if j < 196 then (if j < 194 then data2793 else (if j < 195 then data2794 else data2795)) else (if j < 198 then (if j < 197 then data2796 else data2797) else (if j < 199 then data2798 else data2799))))))))

def srcTableB13 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src2600 else (if j < 2 then src2601 else src2602)) else (if j < 4 then src2603 else (if j < 5 then src2604 else src2605))) else (if j < 9 then (if j < 7 then src2606 else (if j < 8 then src2607 else src2608)) else (if j < 10 then src2609 else (if j < 11 then src2610 else src2611)))) else (if j < 18 then (if j < 15 then (if j < 13 then src2612 else (if j < 14 then src2613 else src2614)) else (if j < 16 then src2615 else (if j < 17 then src2616 else src2617))) else (if j < 21 then (if j < 19 then src2618 else (if j < 20 then src2619 else src2620)) else (if j < 23 then (if j < 22 then src2621 else src2622) else (if j < 24 then src2623 else src2624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src2625 else (if j < 27 then src2626 else src2627)) else (if j < 29 then src2628 else (if j < 30 then src2629 else src2630))) else (if j < 34 then (if j < 32 then src2631 else (if j < 33 then src2632 else src2633)) else (if j < 35 then src2634 else (if j < 36 then src2635 else src2636)))) else (if j < 43 then (if j < 40 then (if j < 38 then src2637 else (if j < 39 then src2638 else src2639)) else (if j < 41 then src2640 else (if j < 42 then src2641 else src2642))) else (if j < 46 then (if j < 44 then src2643 else (if j < 45 then src2644 else src2645)) else (if j < 48 then (if j < 47 then src2646 else src2647) else (if j < 49 then src2648 else src2649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src2650 else (if j < 52 then src2651 else src2652)) else (if j < 54 then src2653 else (if j < 55 then src2654 else src2655))) else (if j < 59 then (if j < 57 then src2656 else (if j < 58 then src2657 else src2658)) else (if j < 60 then src2659 else (if j < 61 then src2660 else src2661)))) else (if j < 68 then (if j < 65 then (if j < 63 then src2662 else (if j < 64 then src2663 else src2664)) else (if j < 66 then src2665 else (if j < 67 then src2666 else src2667))) else (if j < 71 then (if j < 69 then src2668 else (if j < 70 then src2669 else src2670)) else (if j < 73 then (if j < 72 then src2671 else src2672) else (if j < 74 then src2673 else src2674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src2675 else (if j < 77 then src2676 else src2677)) else (if j < 79 then src2678 else (if j < 80 then src2679 else src2680))) else (if j < 84 then (if j < 82 then src2681 else (if j < 83 then src2682 else src2683)) else (if j < 85 then src2684 else (if j < 86 then src2685 else src2686)))) else (if j < 93 then (if j < 90 then (if j < 88 then src2687 else (if j < 89 then src2688 else src2689)) else (if j < 91 then src2690 else (if j < 92 then src2691 else src2692))) else (if j < 96 then (if j < 94 then src2693 else (if j < 95 then src2694 else src2695)) else (if j < 98 then (if j < 97 then src2696 else src2697) else (if j < 99 then src2698 else src2699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src2700 else (if j < 102 then src2701 else src2702)) else (if j < 104 then src2703 else (if j < 105 then src2704 else src2705))) else (if j < 109 then (if j < 107 then src2706 else (if j < 108 then src2707 else src2708)) else (if j < 110 then src2709 else (if j < 111 then src2710 else src2711)))) else (if j < 118 then (if j < 115 then (if j < 113 then src2712 else (if j < 114 then src2713 else src2714)) else (if j < 116 then src2715 else (if j < 117 then src2716 else src2717))) else (if j < 121 then (if j < 119 then src2718 else (if j < 120 then src2719 else src2720)) else (if j < 123 then (if j < 122 then src2721 else src2722) else (if j < 124 then src2723 else src2724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src2725 else (if j < 127 then src2726 else src2727)) else (if j < 129 then src2728 else (if j < 130 then src2729 else src2730))) else (if j < 134 then (if j < 132 then src2731 else (if j < 133 then src2732 else src2733)) else (if j < 135 then src2734 else (if j < 136 then src2735 else src2736)))) else (if j < 143 then (if j < 140 then (if j < 138 then src2737 else (if j < 139 then src2738 else src2739)) else (if j < 141 then src2740 else (if j < 142 then src2741 else src2742))) else (if j < 146 then (if j < 144 then src2743 else (if j < 145 then src2744 else src2745)) else (if j < 148 then (if j < 147 then src2746 else src2747) else (if j < 149 then src2748 else src2749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src2750 else (if j < 152 then src2751 else src2752)) else (if j < 154 then src2753 else (if j < 155 then src2754 else src2755))) else (if j < 159 then (if j < 157 then src2756 else (if j < 158 then src2757 else src2758)) else (if j < 160 then src2759 else (if j < 161 then src2760 else src2761)))) else (if j < 168 then (if j < 165 then (if j < 163 then src2762 else (if j < 164 then src2763 else src2764)) else (if j < 166 then src2765 else (if j < 167 then src2766 else src2767))) else (if j < 171 then (if j < 169 then src2768 else (if j < 170 then src2769 else src2770)) else (if j < 173 then (if j < 172 then src2771 else src2772) else (if j < 174 then src2773 else src2774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src2775 else (if j < 177 then src2776 else src2777)) else (if j < 179 then src2778 else (if j < 180 then src2779 else src2780))) else (if j < 184 then (if j < 182 then src2781 else (if j < 183 then src2782 else src2783)) else (if j < 185 then src2784 else (if j < 186 then src2785 else src2786)))) else (if j < 193 then (if j < 190 then (if j < 188 then src2787 else (if j < 189 then src2788 else src2789)) else (if j < 191 then src2790 else (if j < 192 then src2791 else src2792))) else (if j < 196 then (if j < 194 then src2793 else (if j < 195 then src2794 else src2795)) else (if j < 198 then (if j < 197 then src2796 else src2797) else (if j < 199 then src2798 else src2799))))))))

def dstTableB13 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst2600 else (if j < 2 then dst2601 else dst2602)) else (if j < 4 then dst2603 else (if j < 5 then dst2604 else dst2605))) else (if j < 9 then (if j < 7 then dst2606 else (if j < 8 then dst2607 else dst2608)) else (if j < 10 then dst2609 else (if j < 11 then dst2610 else dst2611)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst2612 else (if j < 14 then dst2613 else dst2614)) else (if j < 16 then dst2615 else (if j < 17 then dst2616 else dst2617))) else (if j < 21 then (if j < 19 then dst2618 else (if j < 20 then dst2619 else dst2620)) else (if j < 23 then (if j < 22 then dst2621 else dst2622) else (if j < 24 then dst2623 else dst2624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst2625 else (if j < 27 then dst2626 else dst2627)) else (if j < 29 then dst2628 else (if j < 30 then dst2629 else dst2630))) else (if j < 34 then (if j < 32 then dst2631 else (if j < 33 then dst2632 else dst2633)) else (if j < 35 then dst2634 else (if j < 36 then dst2635 else dst2636)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst2637 else (if j < 39 then dst2638 else dst2639)) else (if j < 41 then dst2640 else (if j < 42 then dst2641 else dst2642))) else (if j < 46 then (if j < 44 then dst2643 else (if j < 45 then dst2644 else dst2645)) else (if j < 48 then (if j < 47 then dst2646 else dst2647) else (if j < 49 then dst2648 else dst2649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst2650 else (if j < 52 then dst2651 else dst2652)) else (if j < 54 then dst2653 else (if j < 55 then dst2654 else dst2655))) else (if j < 59 then (if j < 57 then dst2656 else (if j < 58 then dst2657 else dst2658)) else (if j < 60 then dst2659 else (if j < 61 then dst2660 else dst2661)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst2662 else (if j < 64 then dst2663 else dst2664)) else (if j < 66 then dst2665 else (if j < 67 then dst2666 else dst2667))) else (if j < 71 then (if j < 69 then dst2668 else (if j < 70 then dst2669 else dst2670)) else (if j < 73 then (if j < 72 then dst2671 else dst2672) else (if j < 74 then dst2673 else dst2674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst2675 else (if j < 77 then dst2676 else dst2677)) else (if j < 79 then dst2678 else (if j < 80 then dst2679 else dst2680))) else (if j < 84 then (if j < 82 then dst2681 else (if j < 83 then dst2682 else dst2683)) else (if j < 85 then dst2684 else (if j < 86 then dst2685 else dst2686)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst2687 else (if j < 89 then dst2688 else dst2689)) else (if j < 91 then dst2690 else (if j < 92 then dst2691 else dst2692))) else (if j < 96 then (if j < 94 then dst2693 else (if j < 95 then dst2694 else dst2695)) else (if j < 98 then (if j < 97 then dst2696 else dst2697) else (if j < 99 then dst2698 else dst2699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst2700 else (if j < 102 then dst2701 else dst2702)) else (if j < 104 then dst2703 else (if j < 105 then dst2704 else dst2705))) else (if j < 109 then (if j < 107 then dst2706 else (if j < 108 then dst2707 else dst2708)) else (if j < 110 then dst2709 else (if j < 111 then dst2710 else dst2711)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst2712 else (if j < 114 then dst2713 else dst2714)) else (if j < 116 then dst2715 else (if j < 117 then dst2716 else dst2717))) else (if j < 121 then (if j < 119 then dst2718 else (if j < 120 then dst2719 else dst2720)) else (if j < 123 then (if j < 122 then dst2721 else dst2722) else (if j < 124 then dst2723 else dst2724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst2725 else (if j < 127 then dst2726 else dst2727)) else (if j < 129 then dst2728 else (if j < 130 then dst2729 else dst2730))) else (if j < 134 then (if j < 132 then dst2731 else (if j < 133 then dst2732 else dst2733)) else (if j < 135 then dst2734 else (if j < 136 then dst2735 else dst2736)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst2737 else (if j < 139 then dst2738 else dst2739)) else (if j < 141 then dst2740 else (if j < 142 then dst2741 else dst2742))) else (if j < 146 then (if j < 144 then dst2743 else (if j < 145 then dst2744 else dst2745)) else (if j < 148 then (if j < 147 then dst2746 else dst2747) else (if j < 149 then dst2748 else dst2749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst2750 else (if j < 152 then dst2751 else dst2752)) else (if j < 154 then dst2753 else (if j < 155 then dst2754 else dst2755))) else (if j < 159 then (if j < 157 then dst2756 else (if j < 158 then dst2757 else dst2758)) else (if j < 160 then dst2759 else (if j < 161 then dst2760 else dst2761)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst2762 else (if j < 164 then dst2763 else dst2764)) else (if j < 166 then dst2765 else (if j < 167 then dst2766 else dst2767))) else (if j < 171 then (if j < 169 then dst2768 else (if j < 170 then dst2769 else dst2770)) else (if j < 173 then (if j < 172 then dst2771 else dst2772) else (if j < 174 then dst2773 else dst2774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst2775 else (if j < 177 then dst2776 else dst2777)) else (if j < 179 then dst2778 else (if j < 180 then dst2779 else dst2780))) else (if j < 184 then (if j < 182 then dst2781 else (if j < 183 then dst2782 else dst2783)) else (if j < 185 then dst2784 else (if j < 186 then dst2785 else dst2786)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst2787 else (if j < 189 then dst2788 else dst2789)) else (if j < 191 then dst2790 else (if j < 192 then dst2791 else dst2792))) else (if j < 196 then (if j < 194 then dst2793 else (if j < 195 then dst2794 else dst2795)) else (if j < 198 then (if j < 197 then dst2796 else dst2797) else (if j < 199 then dst2798 else dst2799))))))))

def caseB13 (i : Fin 200) : Cases := ⟨2600 + i.val,by have := i.isLt; omega⟩
lemma tableB13_valid (i : Fin 200) :
    (lookupB13 i.val).Valid (srcTableB13 i.val) (dstTableB13 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data2600
  · exact valid_data2601
  · exact valid_data2602
  · exact valid_data2603
  · exact valid_data2604
  · exact valid_data2605
  · exact valid_data2606
  · exact valid_data2607
  · exact valid_data2608
  · exact valid_data2609
  · exact valid_data2610
  · exact valid_data2611
  · exact valid_data2612
  · exact valid_data2613
  · exact valid_data2614
  · exact valid_data2615
  · exact valid_data2616
  · exact valid_data2617
  · exact valid_data2618
  · exact valid_data2619
  · exact valid_data2620
  · exact valid_data2621
  · exact valid_data2622
  · exact valid_data2623
  · exact valid_data2624
  · exact valid_data2625
  · exact valid_data2626
  · exact valid_data2627
  · exact valid_data2628
  · exact valid_data2629
  · exact valid_data2630
  · exact valid_data2631
  · exact valid_data2632
  · exact valid_data2633
  · exact valid_data2634
  · exact valid_data2635
  · exact valid_data2636
  · exact valid_data2637
  · exact valid_data2638
  · exact valid_data2639
  · exact valid_data2640
  · exact valid_data2641
  · exact valid_data2642
  · exact valid_data2643
  · exact valid_data2644
  · exact valid_data2645
  · exact valid_data2646
  · exact valid_data2647
  · exact valid_data2648
  · exact valid_data2649
  · exact valid_data2650
  · exact valid_data2651
  · exact valid_data2652
  · exact valid_data2653
  · exact valid_data2654
  · exact valid_data2655
  · exact valid_data2656
  · exact valid_data2657
  · exact valid_data2658
  · exact valid_data2659
  · exact valid_data2660
  · exact valid_data2661
  · exact valid_data2662
  · exact valid_data2663
  · exact valid_data2664
  · exact valid_data2665
  · exact valid_data2666
  · exact valid_data2667
  · exact valid_data2668
  · exact valid_data2669
  · exact valid_data2670
  · exact valid_data2671
  · exact valid_data2672
  · exact valid_data2673
  · exact valid_data2674
  · exact valid_data2675
  · exact valid_data2676
  · exact valid_data2677
  · exact valid_data2678
  · exact valid_data2679
  · exact valid_data2680
  · exact valid_data2681
  · exact valid_data2682
  · exact valid_data2683
  · exact valid_data2684
  · exact valid_data2685
  · exact valid_data2686
  · exact valid_data2687
  · exact valid_data2688
  · exact valid_data2689
  · exact valid_data2690
  · exact valid_data2691
  · exact valid_data2692
  · exact valid_data2693
  · exact valid_data2694
  · exact valid_data2695
  · exact valid_data2696
  · exact valid_data2697
  · exact valid_data2698
  · exact valid_data2699
  · exact valid_data2700
  · exact valid_data2701
  · exact valid_data2702
  · exact valid_data2703
  · exact valid_data2704
  · exact valid_data2705
  · exact valid_data2706
  · exact valid_data2707
  · exact valid_data2708
  · exact valid_data2709
  · exact valid_data2710
  · exact valid_data2711
  · exact valid_data2712
  · exact valid_data2713
  · exact valid_data2714
  · exact valid_data2715
  · exact valid_data2716
  · exact valid_data2717
  · exact valid_data2718
  · exact valid_data2719
  · exact valid_data2720
  · exact valid_data2721
  · exact valid_data2722
  · exact valid_data2723
  · exact valid_data2724
  · exact valid_data2725
  · exact valid_data2726
  · exact valid_data2727
  · exact valid_data2728
  · exact valid_data2729
  · exact valid_data2730
  · exact valid_data2731
  · exact valid_data2732
  · exact valid_data2733
  · exact valid_data2734
  · exact valid_data2735
  · exact valid_data2736
  · exact valid_data2737
  · exact valid_data2738
  · exact valid_data2739
  · exact valid_data2740
  · exact valid_data2741
  · exact valid_data2742
  · exact valid_data2743
  · exact valid_data2744
  · exact valid_data2745
  · exact valid_data2746
  · exact valid_data2747
  · exact valid_data2748
  · exact valid_data2749
  · exact valid_data2750
  · exact valid_data2751
  · exact valid_data2752
  · exact valid_data2753
  · exact valid_data2754
  · exact valid_data2755
  · exact valid_data2756
  · exact valid_data2757
  · exact valid_data2758
  · exact valid_data2759
  · exact valid_data2760
  · exact valid_data2761
  · exact valid_data2762
  · exact valid_data2763
  · exact valid_data2764
  · exact valid_data2765
  · exact valid_data2766
  · exact valid_data2767
  · exact valid_data2768
  · exact valid_data2769
  · exact valid_data2770
  · exact valid_data2771
  · exact valid_data2772
  · exact valid_data2773
  · exact valid_data2774
  · exact valid_data2775
  · exact valid_data2776
  · exact valid_data2777
  · exact valid_data2778
  · exact valid_data2779
  · exact valid_data2780
  · exact valid_data2781
  · exact valid_data2782
  · exact valid_data2783
  · exact valid_data2784
  · exact valid_data2785
  · exact valid_data2786
  · exact valid_data2787
  · exact valid_data2788
  · exact valid_data2789
  · exact valid_data2790
  · exact valid_data2791
  · exact valid_data2792
  · exact valid_data2793
  · exact valid_data2794
  · exact valid_data2795
  · exact valid_data2796
  · exact valid_data2797
  · exact valid_data2798
  · exact valid_data2799

lemma srcB13_row : ∀ (i : Fin 200) (e : E),
    srcTableB13 i.val e = caseSource (caseB13 i) e := by decide +kernel

lemma dstB13_row : ∀ (i : Fin 200) (e : E),
    dstTableB13 i.val e = caseTarget (caseB13 i) e := by decide +kernel

lemma sizeB13 : ∀ i : Fin 200, (lookupB13 i.val).size ≤ 5 →
    (lookupB13 i.val).size = 2 ∧
      (⟨caseKey (caseB13 i),caseKey_lt (caseB13 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB13 (i : Fin 200) : Certificate (caseB13 i) := by
  refine ⟨lookupB13 i.val,?_,sizeB13 i⟩
  have hv := tableB13_valid i
  rw [funext (srcB13_row i),funext (dstB13_row i)] at hv
  exact hv
lemma certificateInterval13 : FiniteIntervals.Covers CertificateAt 2600 2800 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 2600 200 (fun i _ => certificateB13 i)
#print axioms certificateInterval13
end Erdos184Work.FiveRows3

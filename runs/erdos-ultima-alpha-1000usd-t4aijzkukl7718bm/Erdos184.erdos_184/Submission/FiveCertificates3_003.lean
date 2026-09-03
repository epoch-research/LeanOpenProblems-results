import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src600 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst600 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle600_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle600_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle600_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle600_3 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def cycle600_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle600_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data600 : PartitionData E W := ⟨6,![cycle600_0,cycle600_1,cycle600_2,cycle600_3,cycle600_4,cycle600_5]⟩
lemma valid_data600 : data600.Valid src600 dst600 Finset.univ := by decide +kernel

def src601 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst601 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle601_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle601_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle601_2 : CycleData E W := ⟨4,![4,23,14,10,16,9],![2,8,28,4,26,16]⟩
def cycle601_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle601_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle601_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data601 : PartitionData E W := ⟨6,![cycle601_0,cycle601_1,cycle601_2,cycle601_3,cycle601_4,cycle601_5]⟩
lemma valid_data601 : data601.Valid src601 dst601 Finset.univ := by decide +kernel

def src602 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst602 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle602_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle602_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle602_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,27,14]⟩
def cycle602_3 : CycleData E W := ⟨3,![4,3,15,16,9],![2,8,6,26,16]⟩
def cycle602_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle602_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data602 : PartitionData E W := ⟨6,![cycle602_0,cycle602_1,cycle602_2,cycle602_3,cycle602_4,cycle602_5]⟩
lemma valid_data602 : data602.Valid src602 dst602 Finset.univ := by decide +kernel

def src603 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst603 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle603_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle603_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle603_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle603_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle603_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle603_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data603 : PartitionData E W := ⟨6,![cycle603_0,cycle603_1,cycle603_2,cycle603_3,cycle603_4,cycle603_5]⟩
lemma valid_data603 : data603.Valid src603 dst603 Finset.univ := by decide +kernel

def src604 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst604 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle604_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle604_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle604_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle604_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle604_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle604_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data604 : PartitionData E W := ⟨6,![cycle604_0,cycle604_1,cycle604_2,cycle604_3,cycle604_4,cycle604_5]⟩
lemma valid_data604 : data604.Valid src604 dst604 Finset.univ := by decide +kernel

def src605 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst605 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle605_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle605_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle605_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,27,14]⟩
def cycle605_3 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle605_4 : CycleData E W := ⟨3,![4,20,13,18,9],![2,8,28,27,16]⟩
def cycle605_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data605 : PartitionData E W := ⟨6,![cycle605_0,cycle605_1,cycle605_2,cycle605_3,cycle605_4,cycle605_5]⟩
lemma valid_data605 : data605.Valid src605 dst605 Finset.univ := by decide +kernel

def src606 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst606 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle606_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle606_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle606_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle606_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle606_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle606_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data606 : PartitionData E W := ⟨6,![cycle606_0,cycle606_1,cycle606_2,cycle606_3,cycle606_4,cycle606_5]⟩
lemma valid_data606 : data606.Valid src606 dst606 Finset.univ := by decide +kernel

def src607 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst607 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle607_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle607_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle607_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle607_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle607_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle607_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data607 : PartitionData E W := ⟨6,![cycle607_0,cycle607_1,cycle607_2,cycle607_3,cycle607_4,cycle607_5]⟩
lemma valid_data607 : data607.Valid src607 dst607 Finset.univ := by decide +kernel

def src608 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst608 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle608_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle608_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle608_2 : CycleData E W := ⟨2,![2,15,12,6],![3,6,27,14]⟩
def cycle608_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle608_4 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle608_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data608 : PartitionData E W := ⟨6,![cycle608_0,cycle608_1,cycle608_2,cycle608_3,cycle608_4,cycle608_5]⟩
lemma valid_data608 : data608.Valid src608 dst608 Finset.univ := by decide +kernel

def src609 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst609 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle609_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle609_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle609_2 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle609_3 : CycleData E W := ⟨3,![10,17,8,21,14],![4,26,16,18,28]⟩
def cycle609_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle609_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data609 : PartitionData E W := ⟨6,![cycle609_0,cycle609_1,cycle609_2,cycle609_3,cycle609_4,cycle609_5]⟩
lemma valid_data609 : data609.Valid src609 dst609 Finset.univ := by decide +kernel

def src610 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst610 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle610_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle610_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle610_2 : CycleData E W := ⟨4,![4,23,14,10,17,9],![2,8,28,4,26,16]⟩
def cycle610_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle610_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle610_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data610 : PartitionData E W := ⟨6,![cycle610_0,cycle610_1,cycle610_2,cycle610_3,cycle610_4,cycle610_5]⟩
lemma valid_data610 : data610.Valid src610 dst610 Finset.univ := by decide +kernel

def src611 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst611 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle611_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle611_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle611_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle611_3 : CycleData E W := ⟨4,![4,20,14,10,17,9],![2,8,28,4,26,16]⟩
def cycle611_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle611_5 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def data611 : PartitionData E W := ⟨6,![cycle611_0,cycle611_1,cycle611_2,cycle611_3,cycle611_4,cycle611_5]⟩
lemma valid_data611 : data611.Valid src611 dst611 Finset.univ := by decide +kernel

def src612 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst612 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle612_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle612_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle612_2 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle612_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle612_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle612_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data612 : PartitionData E W := ⟨6,![cycle612_0,cycle612_1,cycle612_2,cycle612_3,cycle612_4,cycle612_5]⟩
lemma valid_data612 : data612.Valid src612 dst612 Finset.univ := by decide +kernel

def src613 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst613 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle613_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle613_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle613_2 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle613_3 : CycleData E W := ⟨3,![6,12,23,20,7],![3,14,28,8,18]⟩
def cycle613_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle613_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data613 : PartitionData E W := ⟨6,![cycle613_0,cycle613_1,cycle613_2,cycle613_3,cycle613_4,cycle613_5]⟩
lemma valid_data613 : data613.Valid src613 dst613 Finset.univ := by decide +kernel

def src614 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst614 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle614_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle614_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle614_2 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle614_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle614_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def cycle614_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data614 : PartitionData E W := ⟨6,![cycle614_0,cycle614_1,cycle614_2,cycle614_3,cycle614_4,cycle614_5]⟩
lemma valid_data614 : data614.Valid src614 dst614 Finset.univ := by decide +kernel

def src615 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst615 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle615_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle615_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle615_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle615_3 : CycleData E W := ⟨4,![4,20,21,13,16,9],![2,8,18,28,27,16]⟩
def cycle615_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle615_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data615 : PartitionData E W := ⟨6,![cycle615_0,cycle615_1,cycle615_2,cycle615_3,cycle615_4,cycle615_5]⟩
lemma valid_data615 : data615.Valid src615 dst615 Finset.univ := by decide +kernel

def src616 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst616 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle616_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle616_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle616_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle616_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle616_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle616_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data616 : PartitionData E W := ⟨6,![cycle616_0,cycle616_1,cycle616_2,cycle616_3,cycle616_4,cycle616_5]⟩
lemma valid_data616 : data616.Valid src616 dst616 Finset.univ := by decide +kernel

def src617 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst617 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle617_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle617_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle617_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle617_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle617_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle617_5 : CycleData E W := ⟨3,![11,18,22,21,12],![14,26,38,18,28]⟩
def data617 : PartitionData E W := ⟨6,![cycle617_0,cycle617_1,cycle617_2,cycle617_3,cycle617_4,cycle617_5]⟩
lemma valid_data617 : data617.Valid src617 dst617 Finset.univ := by decide +kernel

def src618 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst618 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle618_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle618_1 : CycleData E W := ⟨3,![1,14,16,15,2],![3,4,27,16,6]⟩
def cycle618_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle618_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle618_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle618_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data618 : PartitionData E W := ⟨6,![cycle618_0,cycle618_1,cycle618_2,cycle618_3,cycle618_4,cycle618_5]⟩
lemma valid_data618 : data618.Valid src618 dst618 Finset.univ := by decide +kernel

def src619 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst619 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle619_0 : CycleData E W := ⟨2,![0,14,16,9],![2,4,27,16]⟩
def cycle619_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle619_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle619_3 : CycleData E W := ⟨3,![3,20,21,18,19],![6,8,18,38,26]⟩
def cycle619_4 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle619_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data619 : PartitionData E W := ⟨6,![cycle619_0,cycle619_1,cycle619_2,cycle619_3,cycle619_4,cycle619_5]⟩
lemma valid_data619 : data619.Valid src619 dst619 Finset.univ := by decide +kernel

def src620 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst620 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle620_0 : CycleData E W := ⟨2,![0,14,16,9],![2,4,27,16]⟩
def cycle620_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,26,14]⟩
def cycle620_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle620_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle620_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle620_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,27,38]⟩
def data620 : PartitionData E W := ⟨6,![cycle620_0,cycle620_1,cycle620_2,cycle620_3,cycle620_4,cycle620_5]⟩
lemma valid_data620 : data620.Valid src620 dst620 Finset.univ := by decide +kernel

def src621 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst621 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle621_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle621_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle621_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle621_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle621_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle621_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data621 : PartitionData E W := ⟨6,![cycle621_0,cycle621_1,cycle621_2,cycle621_3,cycle621_4,cycle621_5]⟩
lemma valid_data621 : data621.Valid src621 dst621 Finset.univ := by decide +kernel

def src622 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst622 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle622_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle622_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle622_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle622_3 : CycleData E W := ⟨3,![4,20,21,16,9],![2,8,18,38,16]⟩
def cycle622_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle622_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data622 : PartitionData E W := ⟨6,![cycle622_0,cycle622_1,cycle622_2,cycle622_3,cycle622_4,cycle622_5]⟩
lemma valid_data622 : data622.Valid src622 dst622 Finset.univ := by decide +kernel

def src623 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst623 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle623_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle623_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle623_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle623_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle623_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle623_5 : CycleData E W := ⟨3,![11,17,22,21,12],![14,26,38,18,28]⟩
def data623 : PartitionData E W := ⟨6,![cycle623_0,cycle623_1,cycle623_2,cycle623_3,cycle623_4,cycle623_5]⟩
lemma valid_data623 : data623.Valid src623 dst623 Finset.univ := by decide +kernel

def src624 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst624 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle624_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle624_1 : CycleData E W := ⟨4,![2,15,11,12,21,7],![3,6,26,14,28,18]⟩
def cycle624_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle624_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle624_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle624_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data624 : PartitionData E W := ⟨6,![cycle624_0,cycle624_1,cycle624_2,cycle624_3,cycle624_4,cycle624_5]⟩
lemma valid_data624 : data624.Valid src624 dst624 Finset.univ := by decide +kernel

def src625 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst625 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle625_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle625_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle625_2 : CycleData E W := ⟨3,![3,23,12,11,15],![6,8,28,14,26]⟩
def cycle625_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle625_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle625_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data625 : PartitionData E W := ⟨6,![cycle625_0,cycle625_1,cycle625_2,cycle625_3,cycle625_4,cycle625_5]⟩
lemma valid_data625 : data625.Valid src625 dst625 Finset.univ := by decide +kernel

def src626 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst626 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle626_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,18,16]⟩
def cycle626_1 : CycleData E W := ⟨2,![2,15,11,6],![3,6,26,14]⟩
def cycle626_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle626_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle626_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle626_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data626 : PartitionData E W := ⟨6,![cycle626_0,cycle626_1,cycle626_2,cycle626_3,cycle626_4,cycle626_5]⟩
lemma valid_data626 : data626.Valid src626 dst626 Finset.univ := by decide +kernel

def src627 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst627 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle627_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle627_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle627_2 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle627_3 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def cycle627_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle627_5 : CycleData E W := ⟨3,![15,11,12,22,19],![6,26,14,28,38]⟩
def data627 : PartitionData E W := ⟨6,![cycle627_0,cycle627_1,cycle627_2,cycle627_3,cycle627_4,cycle627_5]⟩
lemma valid_data627 : data627.Valid src627 dst627 Finset.univ := by decide +kernel

def src628 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst628 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle628_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle628_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle628_2 : CycleData E W := ⟨3,![4,23,13,17,9],![2,8,28,27,16]⟩
def cycle628_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle628_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle628_5 : CycleData E W := ⟨3,![15,11,12,22,19],![6,26,14,28,38]⟩
def data628 : PartitionData E W := ⟨6,![cycle628_0,cycle628_1,cycle628_2,cycle628_3,cycle628_4,cycle628_5]⟩
lemma valid_data628 : data628.Valid src628 dst628 Finset.univ := by decide +kernel

def src629 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst629 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle629_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle629_1 : CycleData E W := ⟨4,![2,15,11,12,21,7],![3,6,26,14,28,18]⟩
def cycle629_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle629_3 : CycleData E W := ⟨3,![4,20,13,17,9],![2,8,28,27,16]⟩
def cycle629_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle629_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data629 : PartitionData E W := ⟨6,![cycle629_0,cycle629_1,cycle629_2,cycle629_3,cycle629_4,cycle629_5]⟩
lemma valid_data629 : data629.Valid src629 dst629 Finset.univ := by decide +kernel

def src630 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst630 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle630_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle630_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle630_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle630_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle630_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle630_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data630 : PartitionData E W := ⟨6,![cycle630_0,cycle630_1,cycle630_2,cycle630_3,cycle630_4,cycle630_5]⟩
lemma valid_data630 : data630.Valid src630 dst630 Finset.univ := by decide +kernel

def src631 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst631 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle631_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle631_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle631_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle631_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle631_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle631_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data631 : PartitionData E W := ⟨6,![cycle631_0,cycle631_1,cycle631_2,cycle631_3,cycle631_4,cycle631_5]⟩
lemma valid_data631 : data631.Valid src631 dst631 Finset.univ := by decide +kernel

def src632 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst632 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle632_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle632_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle632_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle632_3 : CycleData E W := ⟨3,![4,20,13,18,9],![2,8,28,27,16]⟩
def cycle632_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle632_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data632 : PartitionData E W := ⟨6,![cycle632_0,cycle632_1,cycle632_2,cycle632_3,cycle632_4,cycle632_5]⟩
lemma valid_data632 : data632.Valid src632 dst632 Finset.univ := by decide +kernel

def src633 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst633 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle633_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle633_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle633_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle633_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle633_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle633_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data633 : PartitionData E W := ⟨6,![cycle633_0,cycle633_1,cycle633_2,cycle633_3,cycle633_4,cycle633_5]⟩
lemma valid_data633 : data633.Valid src633 dst633 Finset.univ := by decide +kernel

def src634 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst634 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle634_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle634_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle634_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle634_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle634_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle634_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data634 : PartitionData E W := ⟨6,![cycle634_0,cycle634_1,cycle634_2,cycle634_3,cycle634_4,cycle634_5]⟩
lemma valid_data634 : data634.Valid src634 dst634 Finset.univ := by decide +kernel

def src635 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst635 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle635_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle635_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,27,6]⟩
def cycle635_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle635_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle635_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle635_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data635 : PartitionData E W := ⟨6,![cycle635_0,cycle635_1,cycle635_2,cycle635_3,cycle635_4,cycle635_5]⟩
lemma valid_data635 : data635.Valid src635 dst635 Finset.univ := by decide +kernel

def src636 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst636 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle636_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle636_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle636_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle636_3 : CycleData E W := ⟨3,![10,16,8,21,14],![4,26,16,18,28]⟩
def cycle636_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle636_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data636 : PartitionData E W := ⟨6,![cycle636_0,cycle636_1,cycle636_2,cycle636_3,cycle636_4,cycle636_5]⟩
lemma valid_data636 : data636.Valid src636 dst636 Finset.univ := by decide +kernel

def src637 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst637 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle637_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle637_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle637_2 : CycleData E W := ⟨4,![4,23,14,10,16,9],![2,8,28,4,26,16]⟩
def cycle637_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle637_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle637_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data637 : PartitionData E W := ⟨6,![cycle637_0,cycle637_1,cycle637_2,cycle637_3,cycle637_4,cycle637_5]⟩
lemma valid_data637 : data637.Valid src637 dst637 Finset.univ := by decide +kernel

def src638 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst638 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle638_0 : CycleData E W := ⟨2,![0,10,16,9],![2,4,26,16]⟩
def cycle638_1 : CycleData E W := ⟨2,![1,14,13,6],![3,4,28,14]⟩
def cycle638_2 : CycleData E W := ⟨3,![2,3,20,21,7],![3,6,8,28,18]⟩
def cycle638_3 : CycleData E W := ⟨3,![4,23,18,12,5],![2,8,38,27,14]⟩
def cycle638_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle638_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def data638 : PartitionData E W := ⟨6,![cycle638_0,cycle638_1,cycle638_2,cycle638_3,cycle638_4,cycle638_5]⟩
lemma valid_data638 : data638.Valid src638 dst638 Finset.univ := by decide +kernel

def src639 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst639 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle639_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle639_1 : CycleData E W := ⟨4,![2,15,12,13,21,7],![3,6,27,14,28,18]⟩
def cycle639_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle639_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle639_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle639_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data639 : PartitionData E W := ⟨6,![cycle639_0,cycle639_1,cycle639_2,cycle639_3,cycle639_4,cycle639_5]⟩
lemma valid_data639 : data639.Valid src639 dst639 Finset.univ := by decide +kernel

def src640 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst640 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle640_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle640_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle640_2 : CycleData E W := ⟨3,![3,23,13,12,15],![6,8,28,14,27]⟩
def cycle640_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle640_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle640_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data640 : PartitionData E W := ⟨6,![cycle640_0,cycle640_1,cycle640_2,cycle640_3,cycle640_4,cycle640_5]⟩
lemma valid_data640 : data640.Valid src640 dst640 Finset.univ := by decide +kernel

def src641 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst641 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle641_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,18,16]⟩
def cycle641_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,27,14]⟩
def cycle641_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle641_3 : CycleData E W := ⟨2,![4,20,13,5],![2,8,28,14]⟩
def cycle641_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def cycle641_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data641 : PartitionData E W := ⟨6,![cycle641_0,cycle641_1,cycle641_2,cycle641_3,cycle641_4,cycle641_5]⟩
lemma valid_data641 : data641.Valid src641 dst641 Finset.univ := by decide +kernel

def src642 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst642 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle642_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle642_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle642_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle642_3 : CycleData E W := ⟨4,![4,20,21,11,16,9],![2,8,18,28,26,16]⟩
def cycle642_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle642_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data642 : PartitionData E W := ⟨6,![cycle642_0,cycle642_1,cycle642_2,cycle642_3,cycle642_4,cycle642_5]⟩
lemma valid_data642 : data642.Valid src642 dst642 Finset.univ := by decide +kernel

def src643 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst643 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle643_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle643_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle643_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle643_3 : CycleData E W := ⟨3,![4,23,11,16,9],![2,8,28,26,16]⟩
def cycle643_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle643_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data643 : PartitionData E W := ⟨6,![cycle643_0,cycle643_1,cycle643_2,cycle643_3,cycle643_4,cycle643_5]⟩
lemma valid_data643 : data643.Valid src643 dst643 Finset.univ := by decide +kernel

def src644 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst644 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle644_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle644_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle644_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle644_3 : CycleData E W := ⟨3,![4,20,11,16,9],![2,8,28,26,16]⟩
def cycle644_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle644_5 : CycleData E W := ⟨3,![12,21,22,18,13],![14,28,18,38,27]⟩
def data644 : PartitionData E W := ⟨6,![cycle644_0,cycle644_1,cycle644_2,cycle644_3,cycle644_4,cycle644_5]⟩
lemma valid_data644 : data644.Valid src644 dst644 Finset.univ := by decide +kernel

def src645 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst645 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle645_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle645_1 : CycleData E W := ⟨3,![1,10,16,15,2],![3,4,26,16,6]⟩
def cycle645_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle645_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle645_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle645_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data645 : PartitionData E W := ⟨6,![cycle645_0,cycle645_1,cycle645_2,cycle645_3,cycle645_4,cycle645_5]⟩
lemma valid_data645 : data645.Valid src645 dst645 Finset.univ := by decide +kernel

def src646 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst646 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle646_0 : CycleData E W := ⟨2,![0,10,16,9],![2,4,26,16]⟩
def cycle646_1 : CycleData E W := ⟨2,![1,14,13,6],![3,4,27,14]⟩
def cycle646_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle646_3 : CycleData E W := ⟨3,![3,20,21,18,19],![6,8,18,38,27]⟩
def cycle646_4 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle646_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data646 : PartitionData E W := ⟨6,![cycle646_0,cycle646_1,cycle646_2,cycle646_3,cycle646_4,cycle646_5]⟩
lemma valid_data646 : data646.Valid src646 dst646 Finset.univ := by decide +kernel

def src647 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst647 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle647_0 : CycleData E W := ⟨2,![0,10,16,9],![2,4,26,16]⟩
def cycle647_1 : CycleData E W := ⟨2,![1,14,13,6],![3,4,27,14]⟩
def cycle647_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle647_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle647_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle647_5 : CycleData E W := ⟨2,![21,11,17,22],![18,28,26,38]⟩
def data647 : PartitionData E W := ⟨6,![cycle647_0,cycle647_1,cycle647_2,cycle647_3,cycle647_4,cycle647_5]⟩
lemma valid_data647 : data647.Valid src647 dst647 Finset.univ := by decide +kernel

def src648 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst648 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle648_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle648_1 : CycleData E W := ⟨2,![1,10,19,2],![3,4,26,6]⟩
def cycle648_2 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle648_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle648_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle648_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data648 : PartitionData E W := ⟨6,![cycle648_0,cycle648_1,cycle648_2,cycle648_3,cycle648_4,cycle648_5]⟩
lemma valid_data648 : data648.Valid src648 dst648 Finset.univ := by decide +kernel

def src649 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst649 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle649_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle649_1 : CycleData E W := ⟨2,![1,10,19,2],![3,4,26,6]⟩
def cycle649_2 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle649_3 : CycleData E W := ⟨3,![6,12,23,20,7],![3,14,28,8,18]⟩
def cycle649_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle649_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data649 : PartitionData E W := ⟨6,![cycle649_0,cycle649_1,cycle649_2,cycle649_3,cycle649_4,cycle649_5]⟩
lemma valid_data649 : data649.Valid src649 dst649 Finset.univ := by decide +kernel

def src650 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst650 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle650_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle650_1 : CycleData E W := ⟨2,![1,10,19,2],![3,4,26,6]⟩
def cycle650_2 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle650_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle650_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def cycle650_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data650 : PartitionData E W := ⟨6,![cycle650_0,cycle650_1,cycle650_2,cycle650_3,cycle650_4,cycle650_5]⟩
lemma valid_data650 : data650.Valid src650 dst650 Finset.univ := by decide +kernel

def src651 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst651 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle651_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle651_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle651_2 : CycleData E W := ⟨3,![3,20,21,11,19],![6,8,18,28,26]⟩
def cycle651_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle651_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle651_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data651 : PartitionData E W := ⟨6,![cycle651_0,cycle651_1,cycle651_2,cycle651_3,cycle651_4,cycle651_5]⟩
lemma valid_data651 : data651.Valid src651 dst651 Finset.univ := by decide +kernel

def src652 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst652 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle652_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle652_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle652_2 : CycleData E W := ⟨2,![3,23,11,19],![6,8,28,26]⟩
def cycle652_3 : CycleData E W := ⟨3,![4,20,21,16,9],![2,8,18,38,16]⟩
def cycle652_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle652_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data652 : PartitionData E W := ⟨6,![cycle652_0,cycle652_1,cycle652_2,cycle652_3,cycle652_4,cycle652_5]⟩
lemma valid_data652 : data652.Valid src652 dst652 Finset.univ := by decide +kernel

def src653 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst653 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle653_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle653_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle653_2 : CycleData E W := ⟨2,![3,20,11,19],![6,8,28,26]⟩
def cycle653_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle653_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle653_5 : CycleData E W := ⟨3,![12,21,22,17,13],![14,28,18,38,27]⟩
def data653 : PartitionData E W := ⟨6,![cycle653_0,cycle653_1,cycle653_2,cycle653_3,cycle653_4,cycle653_5]⟩
lemma valid_data653 : data653.Valid src653 dst653 Finset.univ := by decide +kernel

def src654 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst654 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle654_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle654_1 : CycleData E W := ⟨3,![2,15,11,21,7],![3,6,26,28,18]⟩
def cycle654_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle654_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle654_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle654_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data654 : PartitionData E W := ⟨6,![cycle654_0,cycle654_1,cycle654_2,cycle654_3,cycle654_4,cycle654_5]⟩
lemma valid_data654 : data654.Valid src654 dst654 Finset.univ := by decide +kernel

def src655 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst655 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle655_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle655_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle655_2 : CycleData E W := ⟨2,![3,23,11,15],![6,8,28,26]⟩
def cycle655_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle655_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle655_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data655 : PartitionData E W := ⟨6,![cycle655_0,cycle655_1,cycle655_2,cycle655_3,cycle655_4,cycle655_5]⟩
lemma valid_data655 : data655.Valid src655 dst655 Finset.univ := by decide +kernel

def src656 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst656 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle656_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle656_1 : CycleData E W := ⟨2,![1,10,15,2],![3,4,26,6]⟩
def cycle656_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle656_3 : CycleData E W := ⟨3,![4,20,11,16,9],![2,8,28,26,16]⟩
def cycle656_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle656_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data656 : PartitionData E W := ⟨6,![cycle656_0,cycle656_1,cycle656_2,cycle656_3,cycle656_4,cycle656_5]⟩
lemma valid_data656 : data656.Valid src656 dst656 Finset.univ := by decide +kernel

def src657 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst657 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle657_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle657_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle657_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle657_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle657_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle657_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data657 : PartitionData E W := ⟨6,![cycle657_0,cycle657_1,cycle657_2,cycle657_3,cycle657_4,cycle657_5]⟩
lemma valid_data657 : data657.Valid src657 dst657 Finset.univ := by decide +kernel

def src658 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst658 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle658_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle658_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle658_2 : CycleData E W := ⟨3,![4,23,11,16,9],![2,8,28,26,16]⟩
def cycle658_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle658_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle658_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data658 : PartitionData E W := ⟨6,![cycle658_0,cycle658_1,cycle658_2,cycle658_3,cycle658_4,cycle658_5]⟩
lemma valid_data658 : data658.Valid src658 dst658 Finset.univ := by decide +kernel

def src659 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst659 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle659_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle659_1 : CycleData E W := ⟨2,![1,10,15,2],![3,4,26,6]⟩
def cycle659_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle659_3 : CycleData E W := ⟨3,![4,20,11,16,9],![2,8,28,26,16]⟩
def cycle659_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle659_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data659 : PartitionData E W := ⟨6,![cycle659_0,cycle659_1,cycle659_2,cycle659_3,cycle659_4,cycle659_5]⟩
lemma valid_data659 : data659.Valid src659 dst659 Finset.univ := by decide +kernel

def src660 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst660 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle660_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle660_1 : CycleData E W := ⟨4,![2,15,13,12,21,7],![3,6,27,14,28,18]⟩
def cycle660_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle660_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle660_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle660_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data660 : PartitionData E W := ⟨6,![cycle660_0,cycle660_1,cycle660_2,cycle660_3,cycle660_4,cycle660_5]⟩
lemma valid_data660 : data660.Valid src660 dst660 Finset.univ := by decide +kernel

def src661 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst661 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle661_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle661_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle661_2 : CycleData E W := ⟨3,![3,23,12,13,15],![6,8,28,14,27]⟩
def cycle661_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle661_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle661_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data661 : PartitionData E W := ⟨6,![cycle661_0,cycle661_1,cycle661_2,cycle661_3,cycle661_4,cycle661_5]⟩
lemma valid_data661 : data661.Valid src661 dst661 Finset.univ := by decide +kernel

def src662 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst662 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle662_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,18,16]⟩
def cycle662_1 : CycleData E W := ⟨2,![2,15,13,6],![3,6,27,14]⟩
def cycle662_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle662_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle662_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle662_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data662 : PartitionData E W := ⟨6,![cycle662_0,cycle662_1,cycle662_2,cycle662_3,cycle662_4,cycle662_5]⟩
lemma valid_data662 : data662.Valid src662 dst662 Finset.univ := by decide +kernel

def src663 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst663 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle663_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle663_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle663_2 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle663_3 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def cycle663_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle663_5 : CycleData E W := ⟨3,![15,13,12,22,19],![6,27,14,28,38]⟩
def data663 : PartitionData E W := ⟨6,![cycle663_0,cycle663_1,cycle663_2,cycle663_3,cycle663_4,cycle663_5]⟩
lemma valid_data663 : data663.Valid src663 dst663 Finset.univ := by decide +kernel

def src664 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst664 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle664_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle664_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle664_2 : CycleData E W := ⟨3,![4,23,11,17,9],![2,8,28,26,16]⟩
def cycle664_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle664_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle664_5 : CycleData E W := ⟨3,![15,13,12,22,19],![6,27,14,28,38]⟩
def data664 : PartitionData E W := ⟨6,![cycle664_0,cycle664_1,cycle664_2,cycle664_3,cycle664_4,cycle664_5]⟩
lemma valid_data664 : data664.Valid src664 dst664 Finset.univ := by decide +kernel

def src665 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst665 : E → W := ![4,3,6,8,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle665_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle665_1 : CycleData E W := ⟨4,![2,15,13,12,21,7],![3,6,27,14,28,18]⟩
def cycle665_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle665_3 : CycleData E W := ⟨3,![4,20,11,17,9],![2,8,28,26,16]⟩
def cycle665_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle665_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data665 : PartitionData E W := ⟨6,![cycle665_0,cycle665_1,cycle665_2,cycle665_3,cycle665_4,cycle665_5]⟩
lemma valid_data665 : data665.Valid src665 dst665 Finset.univ := by decide +kernel

def src666 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst666 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle666_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle666_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle666_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle666_3 : CycleData E W := ⟨4,![4,20,21,13,16,9],![2,8,18,28,26,16]⟩
def cycle666_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle666_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data666 : PartitionData E W := ⟨6,![cycle666_0,cycle666_1,cycle666_2,cycle666_3,cycle666_4,cycle666_5]⟩
lemma valid_data666 : data666.Valid src666 dst666 Finset.univ := by decide +kernel

def src667 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst667 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle667_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle667_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle667_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle667_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle667_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle667_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data667 : PartitionData E W := ⟨6,![cycle667_0,cycle667_1,cycle667_2,cycle667_3,cycle667_4,cycle667_5]⟩
lemma valid_data667 : data667.Valid src667 dst667 Finset.univ := by decide +kernel

def src668 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst668 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle668_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle668_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle668_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle668_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle668_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def cycle668_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data668 : PartitionData E W := ⟨6,![cycle668_0,cycle668_1,cycle668_2,cycle668_3,cycle668_4,cycle668_5]⟩
lemma valid_data668 : data668.Valid src668 dst668 Finset.univ := by decide +kernel

def src669 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst669 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle669_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle669_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle669_2 : CycleData E W := ⟨3,![2,15,16,12,6],![3,6,16,26,14]⟩
def cycle669_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle669_4 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle669_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data669 : PartitionData E W := ⟨6,![cycle669_0,cycle669_1,cycle669_2,cycle669_3,cycle669_4,cycle669_5]⟩
lemma valid_data669 : data669.Valid src669 dst669 Finset.univ := by decide +kernel

def src670 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst670 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle670_0 : CycleData E W := ⟨2,![0,14,23,4],![2,4,28,8]⟩
def cycle670_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,27,14]⟩
def cycle670_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle670_3 : CycleData E W := ⟨3,![3,20,21,18,19],![6,8,18,38,27]⟩
def cycle670_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,26,16]⟩
def cycle670_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data670 : PartitionData E W := ⟨6,![cycle670_0,cycle670_1,cycle670_2,cycle670_3,cycle670_4,cycle670_5]⟩
lemma valid_data670 : data670.Valid src670 dst670 Finset.univ := by decide +kernel

def src671 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst671 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle671_0 : CycleData E W := ⟨2,![0,14,20,4],![2,4,28,8]⟩
def cycle671_1 : CycleData E W := ⟨2,![1,10,11,6],![3,4,27,14]⟩
def cycle671_2 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle671_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle671_4 : CycleData E W := ⟨2,![5,12,16,9],![2,14,26,16]⟩
def cycle671_5 : CycleData E W := ⟨2,![21,13,17,22],![18,28,26,38]⟩
def data671 : PartitionData E W := ⟨6,![cycle671_0,cycle671_1,cycle671_2,cycle671_3,cycle671_4,cycle671_5]⟩
lemma valid_data671 : data671.Valid src671 dst671 Finset.univ := by decide +kernel

def src672 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst672 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle672_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle672_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle672_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,26,14]⟩
def cycle672_3 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle672_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle672_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data672 : PartitionData E W := ⟨6,![cycle672_0,cycle672_1,cycle672_2,cycle672_3,cycle672_4,cycle672_5]⟩
lemma valid_data672 : data672.Valid src672 dst672 Finset.univ := by decide +kernel

def src673 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst673 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle673_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle673_1 : CycleData E W := ⟨3,![1,14,23,20,7],![3,4,28,8,18]⟩
def cycle673_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,26,14]⟩
def cycle673_3 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle673_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle673_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data673 : PartitionData E W := ⟨6,![cycle673_0,cycle673_1,cycle673_2,cycle673_3,cycle673_4,cycle673_5]⟩
lemma valid_data673 : data673.Valid src673 dst673 Finset.univ := by decide +kernel

def src674 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst674 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle674_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle674_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle674_2 : CycleData E W := ⟨2,![2,19,12,6],![3,6,26,14]⟩
def cycle674_3 : CycleData E W := ⟨2,![4,3,15,9],![2,8,6,16]⟩
def cycle674_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def cycle674_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,26,38]⟩
def data674 : PartitionData E W := ⟨6,![cycle674_0,cycle674_1,cycle674_2,cycle674_3,cycle674_4,cycle674_5]⟩
lemma valid_data674 : data674.Valid src674 dst674 Finset.univ := by decide +kernel

def src675 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst675 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle675_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle675_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle675_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,26]⟩
def cycle675_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle675_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle675_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data675 : PartitionData E W := ⟨6,![cycle675_0,cycle675_1,cycle675_2,cycle675_3,cycle675_4,cycle675_5]⟩
lemma valid_data675 : data675.Valid src675 dst675 Finset.univ := by decide +kernel

def src676 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst676 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle676_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle676_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle676_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,26]⟩
def cycle676_3 : CycleData E W := ⟨3,![4,20,21,16,9],![2,8,18,38,16]⟩
def cycle676_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle676_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data676 : PartitionData E W := ⟨6,![cycle676_0,cycle676_1,cycle676_2,cycle676_3,cycle676_4,cycle676_5]⟩
lemma valid_data676 : data676.Valid src676 dst676 Finset.univ := by decide +kernel

def src677 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst677 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle677_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle677_1 : CycleData E W := ⟨2,![2,15,8,7],![3,6,16,18]⟩
def cycle677_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,26]⟩
def cycle677_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle677_4 : CycleData E W := ⟨3,![10,17,22,21,14],![4,27,38,18,28]⟩
def cycle677_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data677 : PartitionData E W := ⟨6,![cycle677_0,cycle677_1,cycle677_2,cycle677_3,cycle677_4,cycle677_5]⟩
lemma valid_data677 : data677.Valid src677 dst677 Finset.univ := by decide +kernel

def src678 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst678 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle678_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle678_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,26,28,18]⟩
def cycle678_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle678_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle678_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle678_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data678 : PartitionData E W := ⟨6,![cycle678_0,cycle678_1,cycle678_2,cycle678_3,cycle678_4,cycle678_5]⟩
lemma valid_data678 : data678.Valid src678 dst678 Finset.univ := by decide +kernel

def src679 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst679 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle679_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle679_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle679_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle679_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle679_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle679_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data679 : PartitionData E W := ⟨6,![cycle679_0,cycle679_1,cycle679_2,cycle679_3,cycle679_4,cycle679_5]⟩
lemma valid_data679 : data679.Valid src679 dst679 Finset.univ := by decide +kernel

def src680 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst680 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle680_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle680_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle680_2 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle680_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle680_4 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle680_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data680 : PartitionData E W := ⟨6,![cycle680_0,cycle680_1,cycle680_2,cycle680_3,cycle680_4,cycle680_5]⟩
lemma valid_data680 : data680.Valid src680 dst680 Finset.univ := by decide +kernel

def src681 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst681 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle681_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle681_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle681_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle681_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle681_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle681_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data681 : PartitionData E W := ⟨6,![cycle681_0,cycle681_1,cycle681_2,cycle681_3,cycle681_4,cycle681_5]⟩
lemma valid_data681 : data681.Valid src681 dst681 Finset.univ := by decide +kernel

def src682 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst682 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle682_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle682_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle682_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle682_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle682_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle682_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data682 : PartitionData E W := ⟨6,![cycle682_0,cycle682_1,cycle682_2,cycle682_3,cycle682_4,cycle682_5]⟩
lemma valid_data682 : data682.Valid src682 dst682 Finset.univ := by decide +kernel

def src683 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst683 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle683_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle683_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle683_2 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle683_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle683_4 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle683_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data683 : PartitionData E W := ⟨6,![cycle683_0,cycle683_1,cycle683_2,cycle683_3,cycle683_4,cycle683_5]⟩
lemma valid_data683 : data683.Valid src683 dst683 Finset.univ := by decide +kernel

def src684 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst684 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle684_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle684_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle684_2 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle684_3 : CycleData E W := ⟨3,![10,17,8,21,14],![4,27,16,18,28]⟩
def cycle684_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle684_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data684 : PartitionData E W := ⟨6,![cycle684_0,cycle684_1,cycle684_2,cycle684_3,cycle684_4,cycle684_5]⟩
lemma valid_data684 : data684.Valid src684 dst684 Finset.univ := by decide +kernel

def src685 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst685 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle685_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle685_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle685_2 : CycleData E W := ⟨4,![4,23,14,10,17,9],![2,8,28,4,27,16]⟩
def cycle685_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle685_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle685_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data685 : PartitionData E W := ⟨6,![cycle685_0,cycle685_1,cycle685_2,cycle685_3,cycle685_4,cycle685_5]⟩
lemma valid_data685 : data685.Valid src685 dst685 Finset.univ := by decide +kernel

def src686 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst686 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle686_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle686_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,26,28,18]⟩
def cycle686_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle686_3 : CycleData E W := ⟨4,![4,20,14,10,17,9],![2,8,28,4,27,16]⟩
def cycle686_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle686_5 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def data686 : PartitionData E W := ⟨6,![cycle686_0,cycle686_1,cycle686_2,cycle686_3,cycle686_4,cycle686_5]⟩
lemma valid_data686 : data686.Valid src686 dst686 Finset.univ := by decide +kernel

def src687 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst687 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle687_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle687_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle687_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle687_3 : CycleData E W := ⟨3,![10,18,8,21,14],![4,27,16,18,28]⟩
def cycle687_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle687_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data687 : PartitionData E W := ⟨6,![cycle687_0,cycle687_1,cycle687_2,cycle687_3,cycle687_4,cycle687_5]⟩
lemma valid_data687 : data687.Valid src687 dst687 Finset.univ := by decide +kernel

def src688 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst688 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle688_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle688_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle688_2 : CycleData E W := ⟨4,![4,23,14,10,18,9],![2,8,28,4,27,16]⟩
def cycle688_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle688_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle688_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data688 : PartitionData E W := ⟨6,![cycle688_0,cycle688_1,cycle688_2,cycle688_3,cycle688_4,cycle688_5]⟩
lemma valid_data688 : data688.Valid src688 dst688 Finset.univ := by decide +kernel

def src689 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst689 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle689_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle689_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle689_2 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle689_3 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle689_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle689_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data689 : PartitionData E W := ⟨6,![cycle689_0,cycle689_1,cycle689_2,cycle689_3,cycle689_4,cycle689_5]⟩
lemma valid_data689 : data689.Valid src689 dst689 Finset.univ := by decide +kernel

def src690 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst690 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle690_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle690_1 : CycleData E W := ⟨4,![2,15,12,13,21,7],![3,6,26,14,28,18]⟩
def cycle690_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle690_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle690_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle690_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data690 : PartitionData E W := ⟨6,![cycle690_0,cycle690_1,cycle690_2,cycle690_3,cycle690_4,cycle690_5]⟩
lemma valid_data690 : data690.Valid src690 dst690 Finset.univ := by decide +kernel

def src691 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst691 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle691_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle691_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle691_2 : CycleData E W := ⟨3,![3,23,13,12,15],![6,8,28,14,26]⟩
def cycle691_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle691_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle691_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data691 : PartitionData E W := ⟨6,![cycle691_0,cycle691_1,cycle691_2,cycle691_3,cycle691_4,cycle691_5]⟩
lemma valid_data691 : data691.Valid src691 dst691 Finset.univ := by decide +kernel

def src692 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst692 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle692_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,4,3,18,16]⟩
def cycle692_1 : CycleData E W := ⟨2,![2,15,12,6],![3,6,26,14]⟩
def cycle692_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle692_3 : CycleData E W := ⟨2,![4,20,13,5],![2,8,28,14]⟩
def cycle692_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def cycle692_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data692 : PartitionData E W := ⟨6,![cycle692_0,cycle692_1,cycle692_2,cycle692_3,cycle692_4,cycle692_5]⟩
lemma valid_data692 : data692.Valid src692 dst692 Finset.univ := by decide +kernel

def src693 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst693 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle693_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle693_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle693_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle693_3 : CycleData E W := ⟨3,![10,18,8,21,14],![4,27,16,18,28]⟩
def cycle693_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle693_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data693 : PartitionData E W := ⟨6,![cycle693_0,cycle693_1,cycle693_2,cycle693_3,cycle693_4,cycle693_5]⟩
lemma valid_data693 : data693.Valid src693 dst693 Finset.univ := by decide +kernel

def src694 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst694 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle694_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,14]⟩
def cycle694_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle694_2 : CycleData E W := ⟨4,![4,23,14,10,18,9],![2,8,28,4,27,16]⟩
def cycle694_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle694_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle694_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data694 : PartitionData E W := ⟨6,![cycle694_0,cycle694_1,cycle694_2,cycle694_3,cycle694_4,cycle694_5]⟩
lemma valid_data694 : data694.Valid src694 dst694 Finset.univ := by decide +kernel

def src695 : E → W := ![2,4,3,6,8,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst695 : E → W := ![4,3,6,8,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle695_0 : CycleData E W := ⟨2,![0,10,18,9],![2,4,27,16]⟩
def cycle695_1 : CycleData E W := ⟨2,![1,14,13,6],![3,4,28,14]⟩
def cycle695_2 : CycleData E W := ⟨3,![2,3,20,21,7],![3,6,8,28,18]⟩
def cycle695_3 : CycleData E W := ⟨3,![4,23,16,12,5],![2,8,38,26,14]⟩
def cycle695_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle695_5 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def data695 : PartitionData E W := ⟨6,![cycle695_0,cycle695_1,cycle695_2,cycle695_3,cycle695_4,cycle695_5]⟩
lemma valid_data695 : data695.Valid src695 dst695 Finset.univ := by decide +kernel

def src696 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst696 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle696_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle696_1 : CycleData E W := ⟨2,![1,14,21,8],![3,4,28,18]⟩
def cycle696_2 : CycleData E W := ⟨2,![2,15,16,7],![3,6,26,16]⟩
def cycle696_3 : CycleData E W := ⟨4,![3,23,17,6,12,19],![6,8,38,16,14,27]⟩
def cycle696_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle696_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data696 : PartitionData E W := ⟨6,![cycle696_0,cycle696_1,cycle696_2,cycle696_3,cycle696_4,cycle696_5]⟩
lemma valid_data696 : data696.Valid src696 dst696 Finset.univ := by decide +kernel

def src697 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst697 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle697_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle697_1 : CycleData E W := ⟨3,![1,14,22,21,8],![3,4,28,38,18]⟩
def cycle697_2 : CycleData E W := ⟨2,![2,15,16,7],![3,6,26,16]⟩
def cycle697_3 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle697_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle697_5 : CycleData E W := ⟨2,![6,17,18,12],![14,16,38,27]⟩
def data697 : PartitionData E W := ⟨6,![cycle697_0,cycle697_1,cycle697_2,cycle697_3,cycle697_4,cycle697_5]⟩
lemma valid_data697 : data697.Valid src697 dst697 Finset.univ := by decide +kernel

def src698 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst698 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle698_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle698_1 : CycleData E W := ⟨2,![1,14,21,8],![3,4,28,18]⟩
def cycle698_2 : CycleData E W := ⟨2,![2,15,16,7],![3,6,26,16]⟩
def cycle698_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle698_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle698_5 : CycleData E W := ⟨2,![6,17,18,12],![14,16,38,27]⟩
def data698 : PartitionData E W := ⟨6,![cycle698_0,cycle698_1,cycle698_2,cycle698_3,cycle698_4,cycle698_5]⟩
lemma valid_data698 : data698.Valid src698 dst698 Finset.univ := by decide +kernel

def src699 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst699 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle699_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle699_1 : CycleData E W := ⟨3,![1,14,13,19,2],![3,4,28,27,6]⟩
def cycle699_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle699_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle699_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle699_5 : CycleData E W := ⟨3,![7,17,22,21,8],![3,16,38,28,18]⟩
def data699 : PartitionData E W := ⟨6,![cycle699_0,cycle699_1,cycle699_2,cycle699_3,cycle699_4,cycle699_5]⟩
lemma valid_data699 : data699.Valid src699 dst699 Finset.univ := by decide +kernel

def src700 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst700 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle700_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle700_1 : CycleData E W := ⟨3,![1,14,13,19,2],![3,4,28,27,6]⟩
def cycle700_2 : CycleData E W := ⟨3,![3,23,22,16,15],![6,8,28,38,26]⟩
def cycle700_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle700_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle700_5 : CycleData E W := ⟨2,![7,17,21,8],![3,16,38,18]⟩
def data700 : PartitionData E W := ⟨6,![cycle700_0,cycle700_1,cycle700_2,cycle700_3,cycle700_4,cycle700_5]⟩
lemma valid_data700 : data700.Valid src700 dst700 Finset.univ := by decide +kernel

def src701 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst701 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle701_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle701_1 : CycleData E W := ⟨3,![1,14,13,19,2],![3,4,28,27,6]⟩
def cycle701_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle701_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle701_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle701_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data701 : PartitionData E W := ⟨6,![cycle701_0,cycle701_1,cycle701_2,cycle701_3,cycle701_4,cycle701_5]⟩
lemma valid_data701 : data701.Valid src701 dst701 Finset.univ := by decide +kernel

def src702 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst702 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle702_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle702_1 : CycleData E W := ⟨3,![2,15,13,21,8],![3,6,27,28,18]⟩
def cycle702_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle702_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle702_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle702_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data702 : PartitionData E W := ⟨6,![cycle702_0,cycle702_1,cycle702_2,cycle702_3,cycle702_4,cycle702_5]⟩
lemma valid_data702 : data702.Valid src702 dst702 Finset.univ := by decide +kernel

def src703 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst703 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle703_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle703_1 : CycleData E W := ⟨2,![2,19,21,8],![3,6,38,18]⟩
def cycle703_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle703_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle703_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle703_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data703 : PartitionData E W := ⟨6,![cycle703_0,cycle703_1,cycle703_2,cycle703_3,cycle703_4,cycle703_5]⟩
lemma valid_data703 : data703.Valid src703 dst703 Finset.univ := by decide +kernel

def src704 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst704 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle704_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle704_1 : CycleData E W := ⟨2,![2,15,16,7],![3,6,27,16]⟩
def cycle704_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle704_3 : CycleData E W := ⟨3,![4,20,13,12,5],![2,8,28,27,14]⟩
def cycle704_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle704_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def data704 : PartitionData E W := ⟨6,![cycle704_0,cycle704_1,cycle704_2,cycle704_3,cycle704_4,cycle704_5]⟩
lemma valid_data704 : data704.Valid src704 dst704 Finset.univ := by decide +kernel

def src705 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst705 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle705_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle705_1 : CycleData E W := ⟨4,![2,15,11,12,21,8],![3,6,26,14,28,18]⟩
def cycle705_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle705_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle705_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle705_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data705 : PartitionData E W := ⟨6,![cycle705_0,cycle705_1,cycle705_2,cycle705_3,cycle705_4,cycle705_5]⟩
lemma valid_data705 : data705.Valid src705 dst705 Finset.univ := by decide +kernel

def src706 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst706 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle706_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle706_1 : CycleData E W := ⟨2,![2,19,21,8],![3,6,38,18]⟩
def cycle706_2 : CycleData E W := ⟨3,![3,23,12,11,15],![6,8,28,14,26]⟩
def cycle706_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle706_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle706_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data706 : PartitionData E W := ⟨6,![cycle706_0,cycle706_1,cycle706_2,cycle706_3,cycle706_4,cycle706_5]⟩
lemma valid_data706 : data706.Valid src706 dst706 Finset.univ := by decide +kernel

def src707 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst707 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle707_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle707_1 : CycleData E W := ⟨3,![2,15,11,6,7],![3,6,26,14,16]⟩
def cycle707_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle707_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle707_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle707_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data707 : PartitionData E W := ⟨6,![cycle707_0,cycle707_1,cycle707_2,cycle707_3,cycle707_4,cycle707_5]⟩
lemma valid_data707 : data707.Valid src707 dst707 Finset.univ := by decide +kernel

def src708 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst708 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle708_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle708_1 : CycleData E W := ⟨2,![1,14,18,7],![3,4,27,16]⟩
def cycle708_2 : CycleData E W := ⟨3,![2,19,13,21,8],![3,6,27,28,18]⟩
def cycle708_3 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle708_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle708_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data708 : PartitionData E W := ⟨6,![cycle708_0,cycle708_1,cycle708_2,cycle708_3,cycle708_4,cycle708_5]⟩
lemma valid_data708 : data708.Valid src708 dst708 Finset.univ := by decide +kernel

def src709 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst709 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle709_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle709_1 : CycleData E W := ⟨2,![1,14,18,7],![3,4,27,16]⟩
def cycle709_2 : CycleData E W := ⟨3,![2,15,16,21,8],![3,6,26,38,18]⟩
def cycle709_3 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle709_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle709_5 : CycleData E W := ⟨2,![6,17,22,12],![14,16,38,28]⟩
def data709 : PartitionData E W := ⟨6,![cycle709_0,cycle709_1,cycle709_2,cycle709_3,cycle709_4,cycle709_5]⟩
lemma valid_data709 : data709.Valid src709 dst709 Finset.univ := by decide +kernel

def src710 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst710 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle710_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle710_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle710_2 : CycleData E W := ⟨2,![3,23,16,15],![6,8,38,26]⟩
def cycle710_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle710_4 : CycleData E W := ⟨2,![6,18,13,12],![14,16,27,28]⟩
def cycle710_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data710 : PartitionData E W := ⟨6,![cycle710_0,cycle710_1,cycle710_2,cycle710_3,cycle710_4,cycle710_5]⟩
lemma valid_data710 : data710.Valid src710 dst710 Finset.univ := by decide +kernel

def src711 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst711 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle711_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle711_1 : CycleData E W := ⟨3,![2,15,13,21,8],![3,6,27,28,18]⟩
def cycle711_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle711_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle711_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle711_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data711 : PartitionData E W := ⟨6,![cycle711_0,cycle711_1,cycle711_2,cycle711_3,cycle711_4,cycle711_5]⟩
lemma valid_data711 : data711.Valid src711 dst711 Finset.univ := by decide +kernel

def src712 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst712 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle712_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle712_1 : CycleData E W := ⟨2,![2,19,21,8],![3,6,38,18]⟩
def cycle712_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle712_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle712_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle712_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data712 : PartitionData E W := ⟨6,![cycle712_0,cycle712_1,cycle712_2,cycle712_3,cycle712_4,cycle712_5]⟩
lemma valid_data712 : data712.Valid src712 dst712 Finset.univ := by decide +kernel

def src713 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst713 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle713_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle713_1 : CycleData E W := ⟨2,![2,15,16,7],![3,6,27,16]⟩
def cycle713_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle713_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle713_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle713_5 : CycleData E W := ⟨4,![10,18,22,21,13,14],![4,26,38,18,28,27]⟩
def data713 : PartitionData E W := ⟨6,![cycle713_0,cycle713_1,cycle713_2,cycle713_3,cycle713_4,cycle713_5]⟩
lemma valid_data713 : data713.Valid src713 dst713 Finset.univ := by decide +kernel

def src714 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst714 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle714_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle714_1 : CycleData E W := ⟨3,![2,15,11,21,8],![3,6,26,28,18]⟩
def cycle714_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle714_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle714_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle714_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data714 : PartitionData E W := ⟨6,![cycle714_0,cycle714_1,cycle714_2,cycle714_3,cycle714_4,cycle714_5]⟩
lemma valid_data714 : data714.Valid src714 dst714 Finset.univ := by decide +kernel

def src715 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst715 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle715_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle715_1 : CycleData E W := ⟨2,![2,19,21,8],![3,6,38,18]⟩
def cycle715_2 : CycleData E W := ⟨2,![3,23,11,15],![6,8,28,26]⟩
def cycle715_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle715_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle715_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data715 : PartitionData E W := ⟨6,![cycle715_0,cycle715_1,cycle715_2,cycle715_3,cycle715_4,cycle715_5]⟩
lemma valid_data715 : data715.Valid src715 dst715 Finset.univ := by decide +kernel

def src716 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst716 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle716_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle716_1 : CycleData E W := ⟨2,![2,15,16,7],![3,6,26,16]⟩
def cycle716_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle716_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle716_4 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle716_5 : CycleData E W := ⟨4,![10,11,21,22,18,14],![4,26,28,18,38,27]⟩
def data716 : PartitionData E W := ⟨6,![cycle716_0,cycle716_1,cycle716_2,cycle716_3,cycle716_4,cycle716_5]⟩
lemma valid_data716 : data716.Valid src716 dst716 Finset.univ := by decide +kernel

def src717 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst717 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle717_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle717_1 : CycleData E W := ⟨2,![1,10,15,2],![3,4,26,6]⟩
def cycle717_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle717_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle717_4 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def cycle717_5 : CycleData E W := ⟨3,![7,17,22,21,8],![3,16,38,28,18]⟩
def data717 : PartitionData E W := ⟨6,![cycle717_0,cycle717_1,cycle717_2,cycle717_3,cycle717_4,cycle717_5]⟩
lemma valid_data717 : data717.Valid src717 dst717 Finset.univ := by decide +kernel

def src718 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst718 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle718_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle718_1 : CycleData E W := ⟨2,![1,10,15,2],![3,4,26,6]⟩
def cycle718_2 : CycleData E W := ⟨3,![3,23,22,18,19],![6,8,28,38,27]⟩
def cycle718_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle718_4 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def cycle718_5 : CycleData E W := ⟨2,![7,17,21,8],![3,16,38,18]⟩
def data718 : PartitionData E W := ⟨6,![cycle718_0,cycle718_1,cycle718_2,cycle718_3,cycle718_4,cycle718_5]⟩
lemma valid_data718 : data718.Valid src718 dst718 Finset.univ := by decide +kernel

def src719 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst719 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle719_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle719_1 : CycleData E W := ⟨2,![1,10,15,2],![3,4,26,6]⟩
def cycle719_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle719_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle719_4 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def cycle719_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data719 : PartitionData E W := ⟨6,![cycle719_0,cycle719_1,cycle719_2,cycle719_3,cycle719_4,cycle719_5]⟩
lemma valid_data719 : data719.Valid src719 dst719 Finset.univ := by decide +kernel

def src720 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst720 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle720_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle720_1 : CycleData E W := ⟨4,![2,15,13,12,21,8],![3,6,27,14,28,18]⟩
def cycle720_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle720_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle720_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle720_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data720 : PartitionData E W := ⟨6,![cycle720_0,cycle720_1,cycle720_2,cycle720_3,cycle720_4,cycle720_5]⟩
lemma valid_data720 : data720.Valid src720 dst720 Finset.univ := by decide +kernel

def src721 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst721 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle721_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle721_1 : CycleData E W := ⟨2,![2,19,21,8],![3,6,38,18]⟩
def cycle721_2 : CycleData E W := ⟨3,![3,23,12,13,15],![6,8,28,14,27]⟩
def cycle721_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle721_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle721_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data721 : PartitionData E W := ⟨6,![cycle721_0,cycle721_1,cycle721_2,cycle721_3,cycle721_4,cycle721_5]⟩
lemma valid_data721 : data721.Valid src721 dst721 Finset.univ := by decide +kernel

def src722 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst722 : E → W := ![4,3,6,8,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle722_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle722_1 : CycleData E W := ⟨3,![2,15,13,6,7],![3,6,27,14,16]⟩
def cycle722_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle722_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle722_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle722_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data722 : PartitionData E W := ⟨6,![cycle722_0,cycle722_1,cycle722_2,cycle722_3,cycle722_4,cycle722_5]⟩
lemma valid_data722 : data722.Valid src722 dst722 Finset.univ := by decide +kernel

def src723 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst723 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle723_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle723_1 : CycleData E W := ⟨3,![2,15,13,21,8],![3,6,26,28,18]⟩
def cycle723_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle723_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle723_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle723_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data723 : PartitionData E W := ⟨6,![cycle723_0,cycle723_1,cycle723_2,cycle723_3,cycle723_4,cycle723_5]⟩
lemma valid_data723 : data723.Valid src723 dst723 Finset.univ := by decide +kernel

def src724 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst724 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle724_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,16,14]⟩
def cycle724_1 : CycleData E W := ⟨2,![2,19,21,8],![3,6,38,18]⟩
def cycle724_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle724_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle724_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle724_5 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def data724 : PartitionData E W := ⟨6,![cycle724_0,cycle724_1,cycle724_2,cycle724_3,cycle724_4,cycle724_5]⟩
lemma valid_data724 : data724.Valid src724 dst724 Finset.univ := by decide +kernel

def src725 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst725 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle725_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,18]⟩
def cycle725_1 : CycleData E W := ⟨2,![2,15,16,7],![3,6,26,16]⟩
def cycle725_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle725_3 : CycleData E W := ⟨3,![4,20,13,12,5],![2,8,28,26,14]⟩
def cycle725_4 : CycleData E W := ⟨1,![6,17,11],![14,16,27]⟩
def cycle725_5 : CycleData E W := ⟨3,![10,18,22,21,14],![4,27,38,18,28]⟩
def data725 : PartitionData E W := ⟨6,![cycle725_0,cycle725_1,cycle725_2,cycle725_3,cycle725_4,cycle725_5]⟩
lemma valid_data725 : data725.Valid src725 dst725 Finset.univ := by decide +kernel

def src726 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst726 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle726_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle726_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,28,26,6]⟩
def cycle726_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle726_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle726_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle726_5 : CycleData E W := ⟨3,![7,17,22,21,8],![3,16,38,28,18]⟩
def data726 : PartitionData E W := ⟨6,![cycle726_0,cycle726_1,cycle726_2,cycle726_3,cycle726_4,cycle726_5]⟩
lemma valid_data726 : data726.Valid src726 dst726 Finset.univ := by decide +kernel

def src727 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst727 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle727_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle727_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,28,26,6]⟩
def cycle727_2 : CycleData E W := ⟨3,![3,23,22,18,19],![6,8,28,38,27]⟩
def cycle727_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle727_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle727_5 : CycleData E W := ⟨2,![7,17,21,8],![3,16,38,18]⟩
def data727 : PartitionData E W := ⟨6,![cycle727_0,cycle727_1,cycle727_2,cycle727_3,cycle727_4,cycle727_5]⟩
lemma valid_data727 : data727.Valid src727 dst727 Finset.univ := by decide +kernel

def src728 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst728 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle728_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle728_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,28,26,6]⟩
def cycle728_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle728_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle728_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle728_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data728 : PartitionData E W := ⟨6,![cycle728_0,cycle728_1,cycle728_2,cycle728_3,cycle728_4,cycle728_5]⟩
lemma valid_data728 : data728.Valid src728 dst728 Finset.univ := by decide +kernel

def src729 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst729 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle729_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle729_1 : CycleData E W := ⟨2,![1,14,21,8],![3,4,28,18]⟩
def cycle729_2 : CycleData E W := ⟨3,![2,15,12,6,7],![3,6,26,14,16]⟩
def cycle729_3 : CycleData E W := ⟨3,![3,23,17,18,19],![6,8,38,16,27]⟩
def cycle729_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle729_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data729 : PartitionData E W := ⟨6,![cycle729_0,cycle729_1,cycle729_2,cycle729_3,cycle729_4,cycle729_5]⟩
lemma valid_data729 : data729.Valid src729 dst729 Finset.univ := by decide +kernel

def src730 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst730 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle730_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle730_1 : CycleData E W := ⟨3,![1,14,22,21,8],![3,4,28,38,18]⟩
def cycle730_2 : CycleData E W := ⟨2,![2,19,18,7],![3,6,27,16]⟩
def cycle730_3 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle730_4 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle730_5 : CycleData E W := ⟨2,![6,17,16,12],![14,16,38,26]⟩
def data730 : PartitionData E W := ⟨6,![cycle730_0,cycle730_1,cycle730_2,cycle730_3,cycle730_4,cycle730_5]⟩
lemma valid_data730 : data730.Valid src730 dst730 Finset.univ := by decide +kernel

def src731 : E → W := ![2,4,3,6,8,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst731 : E → W := ![4,3,6,8,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle731_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle731_1 : CycleData E W := ⟨2,![1,14,21,8],![3,4,28,18]⟩
def cycle731_2 : CycleData E W := ⟨2,![2,19,18,7],![3,6,27,16]⟩
def cycle731_3 : CycleData E W := ⟨2,![3,20,13,15],![6,8,28,26]⟩
def cycle731_4 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle731_5 : CycleData E W := ⟨2,![6,17,16,12],![14,16,38,26]⟩
def data731 : PartitionData E W := ⟨6,![cycle731_0,cycle731_1,cycle731_2,cycle731_3,cycle731_4,cycle731_5]⟩
lemma valid_data731 : data731.Valid src731 dst731 Finset.univ := by decide +kernel

def src732 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst732 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle732_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle732_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle732_2 : CycleData E W := ⟨3,![4,23,16,11,5],![2,8,38,26,14]⟩
def cycle732_3 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle732_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle732_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data732 : PartitionData E W := ⟨6,![cycle732_0,cycle732_1,cycle732_2,cycle732_3,cycle732_4,cycle732_5]⟩
lemma valid_data732 : data732.Valid src732 dst732 Finset.univ := by decide +kernel

def src733 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst733 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle733_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle733_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle733_2 : CycleData E W := ⟨3,![4,23,14,10,5],![2,8,28,4,14]⟩
def cycle733_3 : CycleData E W := ⟨2,![6,21,16,11],![14,18,38,26]⟩
def cycle733_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle733_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data733 : PartitionData E W := ⟨6,![cycle733_0,cycle733_1,cycle733_2,cycle733_3,cycle733_4,cycle733_5]⟩
lemma valid_data733 : data733.Valid src733 dst733 Finset.univ := by decide +kernel

def src734 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst734 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle734_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle734_1 : CycleData E W := ⟨3,![1,14,13,18,8],![3,4,28,27,16]⟩
def cycle734_2 : CycleData E W := ⟨3,![2,3,20,21,7],![3,6,8,28,18]⟩
def cycle734_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle734_4 : CycleData E W := ⟨2,![6,22,16,11],![14,18,38,26]⟩
def cycle734_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data734 : PartitionData E W := ⟨6,![cycle734_0,cycle734_1,cycle734_2,cycle734_3,cycle734_4,cycle734_5]⟩
lemma valid_data734 : data734.Valid src734 dst734 Finset.univ := by decide +kernel

def src735 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst735 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle735_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle735_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle735_2 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle735_3 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle735_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle735_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data735 : PartitionData E W := ⟨6,![cycle735_0,cycle735_1,cycle735_2,cycle735_3,cycle735_4,cycle735_5]⟩
lemma valid_data735 : data735.Valid src735 dst735 Finset.univ := by decide +kernel

def src736 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst736 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle736_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle736_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle736_2 : CycleData E W := ⟨3,![4,23,14,10,5],![2,8,28,4,14]⟩
def cycle736_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle736_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle736_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data736 : PartitionData E W := ⟨6,![cycle736_0,cycle736_1,cycle736_2,cycle736_3,cycle736_4,cycle736_5]⟩
lemma valid_data736 : data736.Valid src736 dst736 Finset.univ := by decide +kernel

def src737 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst737 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle737_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle737_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle737_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle737_3 : CycleData E W := ⟨3,![4,20,14,10,5],![2,8,28,4,14]⟩
def cycle737_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,26]⟩
def cycle737_5 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def data737 : PartitionData E W := ⟨6,![cycle737_0,cycle737_1,cycle737_2,cycle737_3,cycle737_4,cycle737_5]⟩
lemma valid_data737 : data737.Valid src737 dst737 Finset.univ := by decide +kernel

def src738 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst738 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle738_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle738_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,26,28,18]⟩
def cycle738_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle738_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle738_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,26,16,27]⟩
def cycle738_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data738 : PartitionData E W := ⟨6,![cycle738_0,cycle738_1,cycle738_2,cycle738_3,cycle738_4,cycle738_5]⟩
lemma valid_data738 : data738.Valid src738 dst738 Finset.univ := by decide +kernel

def src739 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst739 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle739_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle739_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle739_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,26]⟩
def cycle739_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle739_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,26,16,27]⟩
def cycle739_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data739 : PartitionData E W := ⟨6,![cycle739_0,cycle739_1,cycle739_2,cycle739_3,cycle739_4,cycle739_5]⟩
lemma valid_data739 : data739.Valid src739 dst739 Finset.univ := by decide +kernel

def src740 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst740 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle740_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle740_1 : CycleData E W := ⟨2,![1,14,17,8],![3,4,27,16]⟩
def cycle740_2 : CycleData E W := ⟨3,![2,15,11,6,7],![3,6,26,14,18]⟩
def cycle740_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle740_4 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,26,16]⟩
def cycle740_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data740 : PartitionData E W := ⟨6,![cycle740_0,cycle740_1,cycle740_2,cycle740_3,cycle740_4,cycle740_5]⟩
lemma valid_data740 : data740.Valid src740 dst740 Finset.univ := by decide +kernel

def src741 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst741 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle741_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle741_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle741_2 : CycleData E W := ⟨3,![4,3,15,16,9],![2,8,6,26,16]⟩
def cycle741_3 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle741_4 : CycleData E W := ⟨3,![7,20,23,17,8],![3,18,8,38,16]⟩
def cycle741_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data741 : PartitionData E W := ⟨6,![cycle741_0,cycle741_1,cycle741_2,cycle741_3,cycle741_4,cycle741_5]⟩
lemma valid_data741 : data741.Valid src741 dst741 Finset.univ := by decide +kernel

def src742 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst742 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle742_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle742_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle742_2 : CycleData E W := ⟨3,![4,3,15,16,9],![2,8,6,26,16]⟩
def cycle742_3 : CycleData E W := ⟨3,![20,6,11,12,23],![8,18,14,26,28]⟩
def cycle742_4 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle742_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data742 : PartitionData E W := ⟨6,![cycle742_0,cycle742_1,cycle742_2,cycle742_3,cycle742_4,cycle742_5]⟩
lemma valid_data742 : data742.Valid src742 dst742 Finset.univ := by decide +kernel

def src743 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst743 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle743_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle743_1 : CycleData E W := ⟨2,![1,14,19,2],![3,4,27,6]⟩
def cycle743_2 : CycleData E W := ⟨3,![4,3,15,16,9],![2,8,6,26,16]⟩
def cycle743_3 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle743_4 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def cycle743_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data743 : PartitionData E W := ⟨6,![cycle743_0,cycle743_1,cycle743_2,cycle743_3,cycle743_4,cycle743_5]⟩
lemma valid_data743 : data743.Valid src743 dst743 Finset.univ := by decide +kernel

def src744 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst744 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle744_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle744_1 : CycleData E W := ⟨2,![1,14,18,8],![3,4,27,16]⟩
def cycle744_2 : CycleData E W := ⟨3,![2,15,11,6,7],![3,6,26,14,18]⟩
def cycle744_3 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle744_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle744_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data744 : PartitionData E W := ⟨6,![cycle744_0,cycle744_1,cycle744_2,cycle744_3,cycle744_4,cycle744_5]⟩
lemma valid_data744 : data744.Valid src744 dst744 Finset.univ := by decide +kernel

def src745 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst745 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle745_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle745_1 : CycleData E W := ⟨2,![1,14,18,8],![3,4,27,16]⟩
def cycle745_2 : CycleData E W := ⟨3,![2,15,11,6,7],![3,6,26,14,18]⟩
def cycle745_3 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle745_4 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle745_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data745 : PartitionData E W := ⟨6,![cycle745_0,cycle745_1,cycle745_2,cycle745_3,cycle745_4,cycle745_5]⟩
lemma valid_data745 : data745.Valid src745 dst745 Finset.univ := by decide +kernel

def src746 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst746 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle746_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle746_1 : CycleData E W := ⟨2,![1,14,18,8],![3,4,27,16]⟩
def cycle746_2 : CycleData E W := ⟨3,![2,15,11,6,7],![3,6,26,14,18]⟩
def cycle746_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle746_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle746_5 : CycleData E W := ⟨2,![21,12,16,22],![18,28,26,38]⟩
def data746 : PartitionData E W := ⟨6,![cycle746_0,cycle746_1,cycle746_2,cycle746_3,cycle746_4,cycle746_5]⟩
lemma valid_data746 : data746.Valid src746 dst746 Finset.univ := by decide +kernel

def src747 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst747 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle747_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle747_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle747_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle747_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle747_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle747_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data747 : PartitionData E W := ⟨6,![cycle747_0,cycle747_1,cycle747_2,cycle747_3,cycle747_4,cycle747_5]⟩
lemma valid_data747 : data747.Valid src747 dst747 Finset.univ := by decide +kernel

def src748 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst748 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle748_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle748_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle748_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle748_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle748_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,26,16,27]⟩
def cycle748_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data748 : PartitionData E W := ⟨6,![cycle748_0,cycle748_1,cycle748_2,cycle748_3,cycle748_4,cycle748_5]⟩
lemma valid_data748 : data748.Valid src748 dst748 Finset.univ := by decide +kernel

def src749 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst749 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle749_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle749_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,27,6]⟩
def cycle749_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle749_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle749_4 : CycleData E W := ⟨3,![7,6,11,17,8],![3,18,14,26,16]⟩
def cycle749_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,26,38]⟩
def data749 : PartitionData E W := ⟨6,![cycle749_0,cycle749_1,cycle749_2,cycle749_3,cycle749_4,cycle749_5]⟩
lemma valid_data749 : data749.Valid src749 dst749 Finset.univ := by decide +kernel

def src750 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst750 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle750_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle750_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle750_2 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle750_3 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle750_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle750_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data750 : PartitionData E W := ⟨6,![cycle750_0,cycle750_1,cycle750_2,cycle750_3,cycle750_4,cycle750_5]⟩
lemma valid_data750 : data750.Valid src750 dst750 Finset.univ := by decide +kernel

def src751 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst751 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle751_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle751_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle751_2 : CycleData E W := ⟨3,![4,23,14,10,5],![2,8,28,4,14]⟩
def cycle751_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,27]⟩
def cycle751_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle751_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data751 : PartitionData E W := ⟨6,![cycle751_0,cycle751_1,cycle751_2,cycle751_3,cycle751_4,cycle751_5]⟩
lemma valid_data751 : data751.Valid src751 dst751 Finset.univ := by decide +kernel

def src752 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst752 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle752_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle752_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,26,28,18]⟩
def cycle752_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle752_3 : CycleData E W := ⟨3,![4,20,14,10,5],![2,8,28,4,14]⟩
def cycle752_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle752_5 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def data752 : PartitionData E W := ⟨6,![cycle752_0,cycle752_1,cycle752_2,cycle752_3,cycle752_4,cycle752_5]⟩
lemma valid_data752 : data752.Valid src752 dst752 Finset.univ := by decide +kernel

def src753 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst753 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle753_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle753_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle753_2 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle753_3 : CycleData E W := ⟨2,![10,6,21,14],![4,14,18,28]⟩
def cycle753_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle753_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data753 : PartitionData E W := ⟨6,![cycle753_0,cycle753_1,cycle753_2,cycle753_3,cycle753_4,cycle753_5]⟩
lemma valid_data753 : data753.Valid src753 dst753 Finset.univ := by decide +kernel

def src754 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst754 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle754_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle754_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle754_2 : CycleData E W := ⟨3,![4,23,14,10,5],![2,8,28,4,14]⟩
def cycle754_3 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,27]⟩
def cycle754_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle754_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data754 : PartitionData E W := ⟨6,![cycle754_0,cycle754_1,cycle754_2,cycle754_3,cycle754_4,cycle754_5]⟩
lemma valid_data754 : data754.Valid src754 dst754 Finset.univ := by decide +kernel

def src755 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst755 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle755_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle755_1 : CycleData E W := ⟨3,![1,14,13,16,8],![3,4,28,26,16]⟩
def cycle755_2 : CycleData E W := ⟨3,![2,3,20,21,7],![3,6,8,28,18]⟩
def cycle755_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle755_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle755_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data755 : PartitionData E W := ⟨6,![cycle755_0,cycle755_1,cycle755_2,cycle755_3,cycle755_4,cycle755_5]⟩
lemma valid_data755 : data755.Valid src755 dst755 Finset.univ := by decide +kernel

def src756 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst756 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle756_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle756_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,26,28,18]⟩
def cycle756_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle756_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle756_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle756_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data756 : PartitionData E W := ⟨6,![cycle756_0,cycle756_1,cycle756_2,cycle756_3,cycle756_4,cycle756_5]⟩
lemma valid_data756 : data756.Valid src756 dst756 Finset.univ := by decide +kernel

def src757 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst757 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle757_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle757_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle757_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,26]⟩
def cycle757_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle757_4 : CycleData E W := ⟨3,![10,11,17,16,14],![4,14,27,16,26]⟩
def cycle757_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data757 : PartitionData E W := ⟨6,![cycle757_0,cycle757_1,cycle757_2,cycle757_3,cycle757_4,cycle757_5]⟩
lemma valid_data757 : data757.Valid src757 dst757 Finset.univ := by decide +kernel

def src758 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst758 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle758_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle758_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle758_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle758_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle758_4 : CycleData E W := ⟨3,![7,6,11,17,8],![3,18,14,27,16]⟩
def cycle758_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data758 : PartitionData E W := ⟨6,![cycle758_0,cycle758_1,cycle758_2,cycle758_3,cycle758_4,cycle758_5]⟩
lemma valid_data758 : data758.Valid src758 dst758 Finset.univ := by decide +kernel

def src759 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst759 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle759_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle759_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle759_2 : CycleData E W := ⟨3,![3,20,6,11,19],![6,8,18,14,27]⟩
def cycle759_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle759_4 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,26,16]⟩
def cycle759_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data759 : PartitionData E W := ⟨6,![cycle759_0,cycle759_1,cycle759_2,cycle759_3,cycle759_4,cycle759_5]⟩
lemma valid_data759 : data759.Valid src759 dst759 Finset.univ := by decide +kernel

def src760 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst760 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle760_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle760_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle760_2 : CycleData E W := ⟨3,![3,20,6,11,19],![6,8,18,14,27]⟩
def cycle760_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle760_4 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle760_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data760 : PartitionData E W := ⟨6,![cycle760_0,cycle760_1,cycle760_2,cycle760_3,cycle760_4,cycle760_5]⟩
lemma valid_data760 : data760.Valid src760 dst760 Finset.univ := by decide +kernel

def src761 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst761 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle761_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle761_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle761_2 : CycleData E W := ⟨2,![3,20,12,19],![6,8,28,27]⟩
def cycle761_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle761_4 : CycleData E W := ⟨2,![6,22,18,11],![14,18,38,27]⟩
def cycle761_5 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,26,16]⟩
def data761 : PartitionData E W := ⟨6,![cycle761_0,cycle761_1,cycle761_2,cycle761_3,cycle761_4,cycle761_5]⟩
lemma valid_data761 : data761.Valid src761 dst761 Finset.univ := by decide +kernel

def src762 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst762 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle762_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle762_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle762_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle762_3 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle762_4 : CycleData E W := ⟨3,![7,20,23,17,8],![3,18,8,38,16]⟩
def cycle762_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data762 : PartitionData E W := ⟨6,![cycle762_0,cycle762_1,cycle762_2,cycle762_3,cycle762_4,cycle762_5]⟩
lemma valid_data762 : data762.Valid src762 dst762 Finset.univ := by decide +kernel

def src763 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst763 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle763_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle763_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle763_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle763_3 : CycleData E W := ⟨3,![20,6,11,12,23],![8,18,14,27,28]⟩
def cycle763_4 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle763_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data763 : PartitionData E W := ⟨6,![cycle763_0,cycle763_1,cycle763_2,cycle763_3,cycle763_4,cycle763_5]⟩
lemma valid_data763 : data763.Valid src763 dst763 Finset.univ := by decide +kernel

def src764 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst764 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle764_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle764_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle764_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle764_3 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,27]⟩
def cycle764_4 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def cycle764_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data764 : PartitionData E W := ⟨6,![cycle764_0,cycle764_1,cycle764_2,cycle764_3,cycle764_4,cycle764_5]⟩
lemma valid_data764 : data764.Valid src764 dst764 Finset.univ := by decide +kernel

def src765 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst765 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle765_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle765_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,27,28,18]⟩
def cycle765_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle765_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle765_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle765_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data765 : PartitionData E W := ⟨6,![cycle765_0,cycle765_1,cycle765_2,cycle765_3,cycle765_4,cycle765_5]⟩
lemma valid_data765 : data765.Valid src765 dst765 Finset.univ := by decide +kernel

def src766 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst766 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle766_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle766_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle766_2 : CycleData E W := ⟨2,![3,23,12,15],![6,8,28,27]⟩
def cycle766_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle766_4 : CycleData E W := ⟨3,![10,11,16,17,14],![4,14,27,16,26]⟩
def cycle766_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data766 : PartitionData E W := ⟨6,![cycle766_0,cycle766_1,cycle766_2,cycle766_3,cycle766_4,cycle766_5]⟩
lemma valid_data766 : data766.Valid src766 dst766 Finset.univ := by decide +kernel

def src767 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst767 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle767_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle767_1 : CycleData E W := ⟨2,![1,14,17,8],![3,4,26,16]⟩
def cycle767_2 : CycleData E W := ⟨3,![2,15,11,6,7],![3,6,27,14,18]⟩
def cycle767_3 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle767_4 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,27,16]⟩
def cycle767_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data767 : PartitionData E W := ⟨6,![cycle767_0,cycle767_1,cycle767_2,cycle767_3,cycle767_4,cycle767_5]⟩
lemma valid_data767 : data767.Valid src767 dst767 Finset.univ := by decide +kernel

def src768 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst768 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle768_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle768_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle768_2 : CycleData E W := ⟨4,![4,23,18,14,10,5],![2,8,38,27,4,14]⟩
def cycle768_3 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle768_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle768_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data768 : PartitionData E W := ⟨6,![cycle768_0,cycle768_1,cycle768_2,cycle768_3,cycle768_4,cycle768_5]⟩
lemma valid_data768 : data768.Valid src768 dst768 Finset.univ := by decide +kernel

def src769 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst769 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle769_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle769_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle769_2 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle769_3 : CycleData E W := ⟨3,![10,6,21,18,14],![4,14,18,38,27]⟩
def cycle769_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle769_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data769 : PartitionData E W := ⟨6,![cycle769_0,cycle769_1,cycle769_2,cycle769_3,cycle769_4,cycle769_5]⟩
lemma valid_data769 : data769.Valid src769 dst769 Finset.univ := by decide +kernel

def src770 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst770 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle770_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle770_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,26,28,18]⟩
def cycle770_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle770_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle770_4 : CycleData E W := ⟨3,![10,6,22,18,14],![4,14,18,38,27]⟩
def cycle770_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data770 : PartitionData E W := ⟨6,![cycle770_0,cycle770_1,cycle770_2,cycle770_3,cycle770_4,cycle770_5]⟩
lemma valid_data770 : data770.Valid src770 dst770 Finset.univ := by decide +kernel

def src771 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst771 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle771_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle771_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle771_2 : CycleData E W := ⟨4,![4,23,18,14,10,5],![2,8,38,27,4,14]⟩
def cycle771_3 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle771_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle771_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data771 : PartitionData E W := ⟨6,![cycle771_0,cycle771_1,cycle771_2,cycle771_3,cycle771_4,cycle771_5]⟩
lemma valid_data771 : data771.Valid src771 dst771 Finset.univ := by decide +kernel

def src772 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst772 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle772_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle772_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle772_2 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle772_3 : CycleData E W := ⟨3,![10,6,21,18,14],![4,14,18,38,27]⟩
def cycle772_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle772_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data772 : PartitionData E W := ⟨6,![cycle772_0,cycle772_1,cycle772_2,cycle772_3,cycle772_4,cycle772_5]⟩
lemma valid_data772 : data772.Valid src772 dst772 Finset.univ := by decide +kernel

def src773 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst773 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle773_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle773_1 : CycleData E W := ⟨3,![1,14,13,15,2],![3,4,27,26,6]⟩
def cycle773_2 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,27]⟩
def cycle773_3 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,26,16]⟩
def cycle773_4 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle773_5 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def data773 : PartitionData E W := ⟨6,![cycle773_0,cycle773_1,cycle773_2,cycle773_3,cycle773_4,cycle773_5]⟩
lemma valid_data773 : data773.Valid src773 dst773 Finset.univ := by decide +kernel

def src774 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst774 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle774_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle774_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle774_2 : CycleData E W := ⟨4,![4,23,16,14,10,5],![2,8,38,26,4,14]⟩
def cycle774_3 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle774_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle774_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data774 : PartitionData E W := ⟨6,![cycle774_0,cycle774_1,cycle774_2,cycle774_3,cycle774_4,cycle774_5]⟩
lemma valid_data774 : data774.Valid src774 dst774 Finset.univ := by decide +kernel

def src775 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst775 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle775_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle775_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle775_2 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle775_3 : CycleData E W := ⟨3,![10,6,21,16,14],![4,14,18,38,26]⟩
def cycle775_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle775_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data775 : PartitionData E W := ⟨6,![cycle775_0,cycle775_1,cycle775_2,cycle775_3,cycle775_4,cycle775_5]⟩
lemma valid_data775 : data775.Valid src775 dst775 Finset.univ := by decide +kernel

def src776 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst776 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle776_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle776_1 : CycleData E W := ⟨2,![1,14,15,2],![3,4,26,6]⟩
def cycle776_2 : CycleData E W := ⟨3,![4,3,19,18,9],![2,8,6,27,16]⟩
def cycle776_3 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle776_4 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def cycle776_5 : CycleData E W := ⟨3,![20,12,13,16,23],![8,28,27,26,38]⟩
def data776 : PartitionData E W := ⟨6,![cycle776_0,cycle776_1,cycle776_2,cycle776_3,cycle776_4,cycle776_5]⟩
lemma valid_data776 : data776.Valid src776 dst776 Finset.univ := by decide +kernel

def src777 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst777 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle777_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle777_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle777_2 : CycleData E W := ⟨4,![4,23,18,14,10,5],![2,8,38,26,4,14]⟩
def cycle777_3 : CycleData E W := ⟨1,![6,21,11],![14,18,28]⟩
def cycle777_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle777_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data777 : PartitionData E W := ⟨6,![cycle777_0,cycle777_1,cycle777_2,cycle777_3,cycle777_4,cycle777_5]⟩
lemma valid_data777 : data777.Valid src777 dst777 Finset.univ := by decide +kernel

def src778 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst778 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle778_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle778_1 : CycleData E W := ⟨2,![2,3,20,7],![3,6,8,18]⟩
def cycle778_2 : CycleData E W := ⟨2,![4,23,11,5],![2,8,28,14]⟩
def cycle778_3 : CycleData E W := ⟨3,![10,6,21,18,14],![4,14,18,38,26]⟩
def cycle778_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle778_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data778 : PartitionData E W := ⟨6,![cycle778_0,cycle778_1,cycle778_2,cycle778_3,cycle778_4,cycle778_5]⟩
lemma valid_data778 : data778.Valid src778 dst778 Finset.univ := by decide +kernel

def src779 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst779 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle779_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle779_1 : CycleData E W := ⟨3,![2,15,12,21,7],![3,6,27,28,18]⟩
def cycle779_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle779_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle779_4 : CycleData E W := ⟨3,![10,6,22,18,14],![4,14,18,38,26]⟩
def cycle779_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data779 : PartitionData E W := ⟨6,![cycle779_0,cycle779_1,cycle779_2,cycle779_3,cycle779_4,cycle779_5]⟩
lemma valid_data779 : data779.Valid src779 dst779 Finset.univ := by decide +kernel

def src780 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst780 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle780_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle780_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle780_2 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle780_3 : CycleData E W := ⟨3,![3,20,6,12,19],![6,8,18,14,27]⟩
def cycle780_4 : CycleData E W := ⟨3,![4,23,17,16,9],![2,8,38,26,16]⟩
def cycle780_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data780 : PartitionData E W := ⟨6,![cycle780_0,cycle780_1,cycle780_2,cycle780_3,cycle780_4,cycle780_5]⟩
lemma valid_data780 : data780.Valid src780 dst780 Finset.univ := by decide +kernel

def src781 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst781 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle781_0 : CycleData E W := ⟨2,![0,10,16,9],![2,4,26,16]⟩
def cycle781_1 : CycleData E W := ⟨3,![1,14,22,21,7],![3,4,28,38,18]⟩
def cycle781_2 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle781_3 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle781_4 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle781_5 : CycleData E W := ⟨2,![11,17,18,12],![14,26,38,27]⟩
def data781 : PartitionData E W := ⟨6,![cycle781_0,cycle781_1,cycle781_2,cycle781_3,cycle781_4,cycle781_5]⟩
lemma valid_data781 : data781.Valid src781 dst781 Finset.univ := by decide +kernel

def src782 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst782 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle782_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle782_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle782_2 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle782_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle782_4 : CycleData E W := ⟨3,![4,23,17,16,9],![2,8,38,26,16]⟩
def cycle782_5 : CycleData E W := ⟨2,![6,22,18,12],![14,18,38,27]⟩
def data782 : PartitionData E W := ⟨6,![cycle782_0,cycle782_1,cycle782_2,cycle782_3,cycle782_4,cycle782_5]⟩
lemma valid_data782 : data782.Valid src782 dst782 Finset.univ := by decide +kernel

def src783 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst783 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle783_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle783_1 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle783_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle783_3 : CycleData E W := ⟨4,![4,20,21,13,16,9],![2,8,18,28,27,16]⟩
def cycle783_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle783_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data783 : PartitionData E W := ⟨6,![cycle783_0,cycle783_1,cycle783_2,cycle783_3,cycle783_4,cycle783_5]⟩
lemma valid_data783 : data783.Valid src783 dst783 Finset.univ := by decide +kernel

def src784 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst784 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle784_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle784_1 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle784_2 : CycleData E W := ⟨2,![3,20,21,19],![6,8,18,38]⟩
def cycle784_3 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle784_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle784_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data784 : PartitionData E W := ⟨6,![cycle784_0,cycle784_1,cycle784_2,cycle784_3,cycle784_4,cycle784_5]⟩
lemma valid_data784 : data784.Valid src784 dst784 Finset.univ := by decide +kernel

def src785 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst785 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle785_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle785_1 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle785_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle785_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle785_4 : CycleData E W := ⟨3,![10,18,22,21,14],![4,26,38,18,28]⟩
def cycle785_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data785 : PartitionData E W := ⟨6,![cycle785_0,cycle785_1,cycle785_2,cycle785_3,cycle785_4,cycle785_5]⟩
lemma valid_data785 : data785.Valid src785 dst785 Finset.univ := by decide +kernel

def src786 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst786 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle786_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle786_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle786_2 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle786_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle786_4 : CycleData E W := ⟨4,![4,20,6,12,16,9],![2,8,18,14,27,16]⟩
def cycle786_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data786 : PartitionData E W := ⟨6,![cycle786_0,cycle786_1,cycle786_2,cycle786_3,cycle786_4,cycle786_5]⟩
lemma valid_data786 : data786.Valid src786 dst786 Finset.univ := by decide +kernel

def src787 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst787 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle787_0 : CycleData E W := ⟨3,![0,10,19,3,4],![2,4,26,6,8]⟩
def cycle787_1 : CycleData E W := ⟨3,![1,14,23,20,7],![3,4,28,8,18]⟩
def cycle787_2 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle787_3 : CycleData E W := ⟨2,![5,12,16,9],![2,14,27,16]⟩
def cycle787_4 : CycleData E W := ⟨2,![6,21,18,11],![14,18,38,26]⟩
def cycle787_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data787 : PartitionData E W := ⟨6,![cycle787_0,cycle787_1,cycle787_2,cycle787_3,cycle787_4,cycle787_5]⟩
lemma valid_data787 : data787.Valid src787 dst787 Finset.univ := by decide +kernel

def src788 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst788 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle788_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle788_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle788_2 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle788_3 : CycleData E W := ⟨2,![3,23,18,19],![6,8,38,26]⟩
def cycle788_4 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle788_5 : CycleData E W := ⟨2,![6,22,17,12],![14,18,38,27]⟩
def data788 : PartitionData E W := ⟨6,![cycle788_0,cycle788_1,cycle788_2,cycle788_3,cycle788_4,cycle788_5]⟩
lemma valid_data788 : data788.Valid src788 dst788 Finset.univ := by decide +kernel

def src789 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst789 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle789_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle789_1 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle789_2 : CycleData E W := ⟨3,![3,20,21,13,19],![6,8,18,28,27]⟩
def cycle789_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle789_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle789_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data789 : PartitionData E W := ⟨6,![cycle789_0,cycle789_1,cycle789_2,cycle789_3,cycle789_4,cycle789_5]⟩
lemma valid_data789 : data789.Valid src789 dst789 Finset.univ := by decide +kernel

def src790 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst790 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle790_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle790_1 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle790_2 : CycleData E W := ⟨2,![3,23,13,19],![6,8,28,27]⟩
def cycle790_3 : CycleData E W := ⟨3,![4,20,21,16,9],![2,8,18,38,16]⟩
def cycle790_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle790_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data790 : PartitionData E W := ⟨6,![cycle790_0,cycle790_1,cycle790_2,cycle790_3,cycle790_4,cycle790_5]⟩
lemma valid_data790 : data790.Valid src790 dst790 Finset.univ := by decide +kernel

def src791 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst791 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle791_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,4,3,18,14]⟩
def cycle791_1 : CycleData E W := ⟨1,![2,15,8],![3,6,16]⟩
def cycle791_2 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle791_3 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle791_4 : CycleData E W := ⟨3,![10,17,22,21,14],![4,26,38,18,28]⟩
def cycle791_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data791 : PartitionData E W := ⟨6,![cycle791_0,cycle791_1,cycle791_2,cycle791_3,cycle791_4,cycle791_5]⟩
lemma valid_data791 : data791.Valid src791 dst791 Finset.univ := by decide +kernel

def src792 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst792 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle792_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle792_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle792_2 : CycleData E W := ⟨2,![2,15,16,8],![3,6,26,16]⟩
def cycle792_3 : CycleData E W := ⟨3,![3,20,6,12,19],![6,8,18,14,27]⟩
def cycle792_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle792_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data792 : PartitionData E W := ⟨6,![cycle792_0,cycle792_1,cycle792_2,cycle792_3,cycle792_4,cycle792_5]⟩
lemma valid_data792 : data792.Valid src792 dst792 Finset.univ := by decide +kernel

def src793 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst793 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle793_0 : CycleData E W := ⟨2,![0,10,16,9],![2,4,26,16]⟩
def cycle793_1 : CycleData E W := ⟨3,![1,14,23,3,2],![3,4,28,8,6]⟩
def cycle793_2 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle793_3 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle793_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle793_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data793 : PartitionData E W := ⟨6,![cycle793_0,cycle793_1,cycle793_2,cycle793_3,cycle793_4,cycle793_5]⟩
lemma valid_data793 : data793.Valid src793 dst793 Finset.univ := by decide +kernel

def src794 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst794 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle794_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle794_1 : CycleData E W := ⟨2,![1,14,21,7],![3,4,28,18]⟩
def cycle794_2 : CycleData E W := ⟨2,![2,15,16,8],![3,6,26,16]⟩
def cycle794_3 : CycleData E W := ⟨2,![3,20,13,19],![6,8,28,27]⟩
def cycle794_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle794_5 : CycleData E W := ⟨2,![6,22,18,12],![14,18,38,27]⟩
def data794 : PartitionData E W := ⟨6,![cycle794_0,cycle794_1,cycle794_2,cycle794_3,cycle794_4,cycle794_5]⟩
lemma valid_data794 : data794.Valid src794 dst794 Finset.univ := by decide +kernel

def src795 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst795 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle795_0 : CycleData E W := ⟨10,![0,10,16,17,8,2,3,20,21,13,12,5],![2,4,26,38,16,3,6,8,18,28,27,14]⟩
def cycle795_1 : CycleData E W := ⟨10,![4,23,22,14,1,7,6,11,15,19,18,9],![2,8,38,28,4,3,18,14,26,6,27,16]⟩
def data795 : PartitionData E W := ⟨2,![cycle795_0,cycle795_1]⟩
lemma valid_data795 : data795.Valid src795 dst795 Finset.univ := by decide +kernel

def src796 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst796 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle796_0 : CycleData E W := ⟨10,![5,12,13,14,10,16,21,20,3,2,8,9],![2,14,27,28,4,26,38,18,8,6,3,16]⟩
def cycle796_1 : CycleData E W := ⟨10,![0,1,7,6,11,15,19,18,17,22,23,4],![2,4,3,18,14,26,6,27,16,38,28,8]⟩
def data796 : PartitionData E W := ⟨2,![cycle796_0,cycle796_1]⟩
lemma valid_data796 : data796.Valid src796 dst796 Finset.univ := by decide +kernel

def src797 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst797 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle797_0 : CycleData E W := ⟨10,![0,1,2,15,16,17,18,12,6,21,20,4],![2,4,3,6,26,38,16,27,14,18,28,8]⟩
def cycle797_1 : CycleData E W := ⟨10,![5,11,10,14,13,19,3,23,22,7,8,9],![2,14,26,4,28,27,6,8,38,18,3,16]⟩
def data797 : PartitionData E W := ⟨2,![cycle797_0,cycle797_1]⟩
lemma valid_data797 : data797.Valid src797 dst797 Finset.univ := by decide +kernel

def src798 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst798 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle798_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle798_1 : CycleData E W := ⟨3,![2,15,13,21,7],![3,6,27,28,18]⟩
def cycle798_2 : CycleData E W := ⟨1,![3,23,19],![6,8,38]⟩
def cycle798_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle798_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle798_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data798 : PartitionData E W := ⟨6,![cycle798_0,cycle798_1,cycle798_2,cycle798_3,cycle798_4,cycle798_5]⟩
lemma valid_data798 : data798.Valid src798 dst798 Finset.univ := by decide +kernel

def src799 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst799 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle799_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle799_1 : CycleData E W := ⟨2,![2,19,21,7],![3,6,38,18]⟩
def cycle799_2 : CycleData E W := ⟨2,![3,23,13,15],![6,8,28,27]⟩
def cycle799_3 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle799_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle799_5 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def data799 : PartitionData E W := ⟨6,![cycle799_0,cycle799_1,cycle799_2,cycle799_3,cycle799_4,cycle799_5]⟩
lemma valid_data799 : data799.Valid src799 dst799 Finset.univ := by decide +kernel

def lookupB3 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data600 else (if j < 2 then data601 else data602)) else (if j < 4 then data603 else (if j < 5 then data604 else data605))) else (if j < 9 then (if j < 7 then data606 else (if j < 8 then data607 else data608)) else (if j < 10 then data609 else (if j < 11 then data610 else data611)))) else (if j < 18 then (if j < 15 then (if j < 13 then data612 else (if j < 14 then data613 else data614)) else (if j < 16 then data615 else (if j < 17 then data616 else data617))) else (if j < 21 then (if j < 19 then data618 else (if j < 20 then data619 else data620)) else (if j < 23 then (if j < 22 then data621 else data622) else (if j < 24 then data623 else data624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data625 else (if j < 27 then data626 else data627)) else (if j < 29 then data628 else (if j < 30 then data629 else data630))) else (if j < 34 then (if j < 32 then data631 else (if j < 33 then data632 else data633)) else (if j < 35 then data634 else (if j < 36 then data635 else data636)))) else (if j < 43 then (if j < 40 then (if j < 38 then data637 else (if j < 39 then data638 else data639)) else (if j < 41 then data640 else (if j < 42 then data641 else data642))) else (if j < 46 then (if j < 44 then data643 else (if j < 45 then data644 else data645)) else (if j < 48 then (if j < 47 then data646 else data647) else (if j < 49 then data648 else data649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data650 else (if j < 52 then data651 else data652)) else (if j < 54 then data653 else (if j < 55 then data654 else data655))) else (if j < 59 then (if j < 57 then data656 else (if j < 58 then data657 else data658)) else (if j < 60 then data659 else (if j < 61 then data660 else data661)))) else (if j < 68 then (if j < 65 then (if j < 63 then data662 else (if j < 64 then data663 else data664)) else (if j < 66 then data665 else (if j < 67 then data666 else data667))) else (if j < 71 then (if j < 69 then data668 else (if j < 70 then data669 else data670)) else (if j < 73 then (if j < 72 then data671 else data672) else (if j < 74 then data673 else data674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data675 else (if j < 77 then data676 else data677)) else (if j < 79 then data678 else (if j < 80 then data679 else data680))) else (if j < 84 then (if j < 82 then data681 else (if j < 83 then data682 else data683)) else (if j < 85 then data684 else (if j < 86 then data685 else data686)))) else (if j < 93 then (if j < 90 then (if j < 88 then data687 else (if j < 89 then data688 else data689)) else (if j < 91 then data690 else (if j < 92 then data691 else data692))) else (if j < 96 then (if j < 94 then data693 else (if j < 95 then data694 else data695)) else (if j < 98 then (if j < 97 then data696 else data697) else (if j < 99 then data698 else data699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data700 else (if j < 102 then data701 else data702)) else (if j < 104 then data703 else (if j < 105 then data704 else data705))) else (if j < 109 then (if j < 107 then data706 else (if j < 108 then data707 else data708)) else (if j < 110 then data709 else (if j < 111 then data710 else data711)))) else (if j < 118 then (if j < 115 then (if j < 113 then data712 else (if j < 114 then data713 else data714)) else (if j < 116 then data715 else (if j < 117 then data716 else data717))) else (if j < 121 then (if j < 119 then data718 else (if j < 120 then data719 else data720)) else (if j < 123 then (if j < 122 then data721 else data722) else (if j < 124 then data723 else data724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data725 else (if j < 127 then data726 else data727)) else (if j < 129 then data728 else (if j < 130 then data729 else data730))) else (if j < 134 then (if j < 132 then data731 else (if j < 133 then data732 else data733)) else (if j < 135 then data734 else (if j < 136 then data735 else data736)))) else (if j < 143 then (if j < 140 then (if j < 138 then data737 else (if j < 139 then data738 else data739)) else (if j < 141 then data740 else (if j < 142 then data741 else data742))) else (if j < 146 then (if j < 144 then data743 else (if j < 145 then data744 else data745)) else (if j < 148 then (if j < 147 then data746 else data747) else (if j < 149 then data748 else data749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data750 else (if j < 152 then data751 else data752)) else (if j < 154 then data753 else (if j < 155 then data754 else data755))) else (if j < 159 then (if j < 157 then data756 else (if j < 158 then data757 else data758)) else (if j < 160 then data759 else (if j < 161 then data760 else data761)))) else (if j < 168 then (if j < 165 then (if j < 163 then data762 else (if j < 164 then data763 else data764)) else (if j < 166 then data765 else (if j < 167 then data766 else data767))) else (if j < 171 then (if j < 169 then data768 else (if j < 170 then data769 else data770)) else (if j < 173 then (if j < 172 then data771 else data772) else (if j < 174 then data773 else data774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data775 else (if j < 177 then data776 else data777)) else (if j < 179 then data778 else (if j < 180 then data779 else data780))) else (if j < 184 then (if j < 182 then data781 else (if j < 183 then data782 else data783)) else (if j < 185 then data784 else (if j < 186 then data785 else data786)))) else (if j < 193 then (if j < 190 then (if j < 188 then data787 else (if j < 189 then data788 else data789)) else (if j < 191 then data790 else (if j < 192 then data791 else data792))) else (if j < 196 then (if j < 194 then data793 else (if j < 195 then data794 else data795)) else (if j < 198 then (if j < 197 then data796 else data797) else (if j < 199 then data798 else data799))))))))

def srcTableB3 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src600 else (if j < 2 then src601 else src602)) else (if j < 4 then src603 else (if j < 5 then src604 else src605))) else (if j < 9 then (if j < 7 then src606 else (if j < 8 then src607 else src608)) else (if j < 10 then src609 else (if j < 11 then src610 else src611)))) else (if j < 18 then (if j < 15 then (if j < 13 then src612 else (if j < 14 then src613 else src614)) else (if j < 16 then src615 else (if j < 17 then src616 else src617))) else (if j < 21 then (if j < 19 then src618 else (if j < 20 then src619 else src620)) else (if j < 23 then (if j < 22 then src621 else src622) else (if j < 24 then src623 else src624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src625 else (if j < 27 then src626 else src627)) else (if j < 29 then src628 else (if j < 30 then src629 else src630))) else (if j < 34 then (if j < 32 then src631 else (if j < 33 then src632 else src633)) else (if j < 35 then src634 else (if j < 36 then src635 else src636)))) else (if j < 43 then (if j < 40 then (if j < 38 then src637 else (if j < 39 then src638 else src639)) else (if j < 41 then src640 else (if j < 42 then src641 else src642))) else (if j < 46 then (if j < 44 then src643 else (if j < 45 then src644 else src645)) else (if j < 48 then (if j < 47 then src646 else src647) else (if j < 49 then src648 else src649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src650 else (if j < 52 then src651 else src652)) else (if j < 54 then src653 else (if j < 55 then src654 else src655))) else (if j < 59 then (if j < 57 then src656 else (if j < 58 then src657 else src658)) else (if j < 60 then src659 else (if j < 61 then src660 else src661)))) else (if j < 68 then (if j < 65 then (if j < 63 then src662 else (if j < 64 then src663 else src664)) else (if j < 66 then src665 else (if j < 67 then src666 else src667))) else (if j < 71 then (if j < 69 then src668 else (if j < 70 then src669 else src670)) else (if j < 73 then (if j < 72 then src671 else src672) else (if j < 74 then src673 else src674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src675 else (if j < 77 then src676 else src677)) else (if j < 79 then src678 else (if j < 80 then src679 else src680))) else (if j < 84 then (if j < 82 then src681 else (if j < 83 then src682 else src683)) else (if j < 85 then src684 else (if j < 86 then src685 else src686)))) else (if j < 93 then (if j < 90 then (if j < 88 then src687 else (if j < 89 then src688 else src689)) else (if j < 91 then src690 else (if j < 92 then src691 else src692))) else (if j < 96 then (if j < 94 then src693 else (if j < 95 then src694 else src695)) else (if j < 98 then (if j < 97 then src696 else src697) else (if j < 99 then src698 else src699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src700 else (if j < 102 then src701 else src702)) else (if j < 104 then src703 else (if j < 105 then src704 else src705))) else (if j < 109 then (if j < 107 then src706 else (if j < 108 then src707 else src708)) else (if j < 110 then src709 else (if j < 111 then src710 else src711)))) else (if j < 118 then (if j < 115 then (if j < 113 then src712 else (if j < 114 then src713 else src714)) else (if j < 116 then src715 else (if j < 117 then src716 else src717))) else (if j < 121 then (if j < 119 then src718 else (if j < 120 then src719 else src720)) else (if j < 123 then (if j < 122 then src721 else src722) else (if j < 124 then src723 else src724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src725 else (if j < 127 then src726 else src727)) else (if j < 129 then src728 else (if j < 130 then src729 else src730))) else (if j < 134 then (if j < 132 then src731 else (if j < 133 then src732 else src733)) else (if j < 135 then src734 else (if j < 136 then src735 else src736)))) else (if j < 143 then (if j < 140 then (if j < 138 then src737 else (if j < 139 then src738 else src739)) else (if j < 141 then src740 else (if j < 142 then src741 else src742))) else (if j < 146 then (if j < 144 then src743 else (if j < 145 then src744 else src745)) else (if j < 148 then (if j < 147 then src746 else src747) else (if j < 149 then src748 else src749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src750 else (if j < 152 then src751 else src752)) else (if j < 154 then src753 else (if j < 155 then src754 else src755))) else (if j < 159 then (if j < 157 then src756 else (if j < 158 then src757 else src758)) else (if j < 160 then src759 else (if j < 161 then src760 else src761)))) else (if j < 168 then (if j < 165 then (if j < 163 then src762 else (if j < 164 then src763 else src764)) else (if j < 166 then src765 else (if j < 167 then src766 else src767))) else (if j < 171 then (if j < 169 then src768 else (if j < 170 then src769 else src770)) else (if j < 173 then (if j < 172 then src771 else src772) else (if j < 174 then src773 else src774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src775 else (if j < 177 then src776 else src777)) else (if j < 179 then src778 else (if j < 180 then src779 else src780))) else (if j < 184 then (if j < 182 then src781 else (if j < 183 then src782 else src783)) else (if j < 185 then src784 else (if j < 186 then src785 else src786)))) else (if j < 193 then (if j < 190 then (if j < 188 then src787 else (if j < 189 then src788 else src789)) else (if j < 191 then src790 else (if j < 192 then src791 else src792))) else (if j < 196 then (if j < 194 then src793 else (if j < 195 then src794 else src795)) else (if j < 198 then (if j < 197 then src796 else src797) else (if j < 199 then src798 else src799))))))))

def dstTableB3 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst600 else (if j < 2 then dst601 else dst602)) else (if j < 4 then dst603 else (if j < 5 then dst604 else dst605))) else (if j < 9 then (if j < 7 then dst606 else (if j < 8 then dst607 else dst608)) else (if j < 10 then dst609 else (if j < 11 then dst610 else dst611)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst612 else (if j < 14 then dst613 else dst614)) else (if j < 16 then dst615 else (if j < 17 then dst616 else dst617))) else (if j < 21 then (if j < 19 then dst618 else (if j < 20 then dst619 else dst620)) else (if j < 23 then (if j < 22 then dst621 else dst622) else (if j < 24 then dst623 else dst624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst625 else (if j < 27 then dst626 else dst627)) else (if j < 29 then dst628 else (if j < 30 then dst629 else dst630))) else (if j < 34 then (if j < 32 then dst631 else (if j < 33 then dst632 else dst633)) else (if j < 35 then dst634 else (if j < 36 then dst635 else dst636)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst637 else (if j < 39 then dst638 else dst639)) else (if j < 41 then dst640 else (if j < 42 then dst641 else dst642))) else (if j < 46 then (if j < 44 then dst643 else (if j < 45 then dst644 else dst645)) else (if j < 48 then (if j < 47 then dst646 else dst647) else (if j < 49 then dst648 else dst649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst650 else (if j < 52 then dst651 else dst652)) else (if j < 54 then dst653 else (if j < 55 then dst654 else dst655))) else (if j < 59 then (if j < 57 then dst656 else (if j < 58 then dst657 else dst658)) else (if j < 60 then dst659 else (if j < 61 then dst660 else dst661)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst662 else (if j < 64 then dst663 else dst664)) else (if j < 66 then dst665 else (if j < 67 then dst666 else dst667))) else (if j < 71 then (if j < 69 then dst668 else (if j < 70 then dst669 else dst670)) else (if j < 73 then (if j < 72 then dst671 else dst672) else (if j < 74 then dst673 else dst674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst675 else (if j < 77 then dst676 else dst677)) else (if j < 79 then dst678 else (if j < 80 then dst679 else dst680))) else (if j < 84 then (if j < 82 then dst681 else (if j < 83 then dst682 else dst683)) else (if j < 85 then dst684 else (if j < 86 then dst685 else dst686)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst687 else (if j < 89 then dst688 else dst689)) else (if j < 91 then dst690 else (if j < 92 then dst691 else dst692))) else (if j < 96 then (if j < 94 then dst693 else (if j < 95 then dst694 else dst695)) else (if j < 98 then (if j < 97 then dst696 else dst697) else (if j < 99 then dst698 else dst699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst700 else (if j < 102 then dst701 else dst702)) else (if j < 104 then dst703 else (if j < 105 then dst704 else dst705))) else (if j < 109 then (if j < 107 then dst706 else (if j < 108 then dst707 else dst708)) else (if j < 110 then dst709 else (if j < 111 then dst710 else dst711)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst712 else (if j < 114 then dst713 else dst714)) else (if j < 116 then dst715 else (if j < 117 then dst716 else dst717))) else (if j < 121 then (if j < 119 then dst718 else (if j < 120 then dst719 else dst720)) else (if j < 123 then (if j < 122 then dst721 else dst722) else (if j < 124 then dst723 else dst724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst725 else (if j < 127 then dst726 else dst727)) else (if j < 129 then dst728 else (if j < 130 then dst729 else dst730))) else (if j < 134 then (if j < 132 then dst731 else (if j < 133 then dst732 else dst733)) else (if j < 135 then dst734 else (if j < 136 then dst735 else dst736)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst737 else (if j < 139 then dst738 else dst739)) else (if j < 141 then dst740 else (if j < 142 then dst741 else dst742))) else (if j < 146 then (if j < 144 then dst743 else (if j < 145 then dst744 else dst745)) else (if j < 148 then (if j < 147 then dst746 else dst747) else (if j < 149 then dst748 else dst749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst750 else (if j < 152 then dst751 else dst752)) else (if j < 154 then dst753 else (if j < 155 then dst754 else dst755))) else (if j < 159 then (if j < 157 then dst756 else (if j < 158 then dst757 else dst758)) else (if j < 160 then dst759 else (if j < 161 then dst760 else dst761)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst762 else (if j < 164 then dst763 else dst764)) else (if j < 166 then dst765 else (if j < 167 then dst766 else dst767))) else (if j < 171 then (if j < 169 then dst768 else (if j < 170 then dst769 else dst770)) else (if j < 173 then (if j < 172 then dst771 else dst772) else (if j < 174 then dst773 else dst774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst775 else (if j < 177 then dst776 else dst777)) else (if j < 179 then dst778 else (if j < 180 then dst779 else dst780))) else (if j < 184 then (if j < 182 then dst781 else (if j < 183 then dst782 else dst783)) else (if j < 185 then dst784 else (if j < 186 then dst785 else dst786)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst787 else (if j < 189 then dst788 else dst789)) else (if j < 191 then dst790 else (if j < 192 then dst791 else dst792))) else (if j < 196 then (if j < 194 then dst793 else (if j < 195 then dst794 else dst795)) else (if j < 198 then (if j < 197 then dst796 else dst797) else (if j < 199 then dst798 else dst799))))))))

def caseB3 (i : Fin 200) : Cases := ⟨600 + i.val,by have := i.isLt; omega⟩
lemma tableB3_valid (i : Fin 200) :
    (lookupB3 i.val).Valid (srcTableB3 i.val) (dstTableB3 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data600
  · exact valid_data601
  · exact valid_data602
  · exact valid_data603
  · exact valid_data604
  · exact valid_data605
  · exact valid_data606
  · exact valid_data607
  · exact valid_data608
  · exact valid_data609
  · exact valid_data610
  · exact valid_data611
  · exact valid_data612
  · exact valid_data613
  · exact valid_data614
  · exact valid_data615
  · exact valid_data616
  · exact valid_data617
  · exact valid_data618
  · exact valid_data619
  · exact valid_data620
  · exact valid_data621
  · exact valid_data622
  · exact valid_data623
  · exact valid_data624
  · exact valid_data625
  · exact valid_data626
  · exact valid_data627
  · exact valid_data628
  · exact valid_data629
  · exact valid_data630
  · exact valid_data631
  · exact valid_data632
  · exact valid_data633
  · exact valid_data634
  · exact valid_data635
  · exact valid_data636
  · exact valid_data637
  · exact valid_data638
  · exact valid_data639
  · exact valid_data640
  · exact valid_data641
  · exact valid_data642
  · exact valid_data643
  · exact valid_data644
  · exact valid_data645
  · exact valid_data646
  · exact valid_data647
  · exact valid_data648
  · exact valid_data649
  · exact valid_data650
  · exact valid_data651
  · exact valid_data652
  · exact valid_data653
  · exact valid_data654
  · exact valid_data655
  · exact valid_data656
  · exact valid_data657
  · exact valid_data658
  · exact valid_data659
  · exact valid_data660
  · exact valid_data661
  · exact valid_data662
  · exact valid_data663
  · exact valid_data664
  · exact valid_data665
  · exact valid_data666
  · exact valid_data667
  · exact valid_data668
  · exact valid_data669
  · exact valid_data670
  · exact valid_data671
  · exact valid_data672
  · exact valid_data673
  · exact valid_data674
  · exact valid_data675
  · exact valid_data676
  · exact valid_data677
  · exact valid_data678
  · exact valid_data679
  · exact valid_data680
  · exact valid_data681
  · exact valid_data682
  · exact valid_data683
  · exact valid_data684
  · exact valid_data685
  · exact valid_data686
  · exact valid_data687
  · exact valid_data688
  · exact valid_data689
  · exact valid_data690
  · exact valid_data691
  · exact valid_data692
  · exact valid_data693
  · exact valid_data694
  · exact valid_data695
  · exact valid_data696
  · exact valid_data697
  · exact valid_data698
  · exact valid_data699
  · exact valid_data700
  · exact valid_data701
  · exact valid_data702
  · exact valid_data703
  · exact valid_data704
  · exact valid_data705
  · exact valid_data706
  · exact valid_data707
  · exact valid_data708
  · exact valid_data709
  · exact valid_data710
  · exact valid_data711
  · exact valid_data712
  · exact valid_data713
  · exact valid_data714
  · exact valid_data715
  · exact valid_data716
  · exact valid_data717
  · exact valid_data718
  · exact valid_data719
  · exact valid_data720
  · exact valid_data721
  · exact valid_data722
  · exact valid_data723
  · exact valid_data724
  · exact valid_data725
  · exact valid_data726
  · exact valid_data727
  · exact valid_data728
  · exact valid_data729
  · exact valid_data730
  · exact valid_data731
  · exact valid_data732
  · exact valid_data733
  · exact valid_data734
  · exact valid_data735
  · exact valid_data736
  · exact valid_data737
  · exact valid_data738
  · exact valid_data739
  · exact valid_data740
  · exact valid_data741
  · exact valid_data742
  · exact valid_data743
  · exact valid_data744
  · exact valid_data745
  · exact valid_data746
  · exact valid_data747
  · exact valid_data748
  · exact valid_data749
  · exact valid_data750
  · exact valid_data751
  · exact valid_data752
  · exact valid_data753
  · exact valid_data754
  · exact valid_data755
  · exact valid_data756
  · exact valid_data757
  · exact valid_data758
  · exact valid_data759
  · exact valid_data760
  · exact valid_data761
  · exact valid_data762
  · exact valid_data763
  · exact valid_data764
  · exact valid_data765
  · exact valid_data766
  · exact valid_data767
  · exact valid_data768
  · exact valid_data769
  · exact valid_data770
  · exact valid_data771
  · exact valid_data772
  · exact valid_data773
  · exact valid_data774
  · exact valid_data775
  · exact valid_data776
  · exact valid_data777
  · exact valid_data778
  · exact valid_data779
  · exact valid_data780
  · exact valid_data781
  · exact valid_data782
  · exact valid_data783
  · exact valid_data784
  · exact valid_data785
  · exact valid_data786
  · exact valid_data787
  · exact valid_data788
  · exact valid_data789
  · exact valid_data790
  · exact valid_data791
  · exact valid_data792
  · exact valid_data793
  · exact valid_data794
  · exact valid_data795
  · exact valid_data796
  · exact valid_data797
  · exact valid_data798
  · exact valid_data799

lemma srcB3_row : ∀ (i : Fin 200) (e : E),
    srcTableB3 i.val e = caseSource (caseB3 i) e := by decide +kernel

lemma dstB3_row : ∀ (i : Fin 200) (e : E),
    dstTableB3 i.val e = caseTarget (caseB3 i) e := by decide +kernel

lemma sizeB3 : ∀ i : Fin 200, (lookupB3 i.val).size ≤ 5 →
    (lookupB3 i.val).size = 2 ∧
      (⟨caseKey (caseB3 i),caseKey_lt (caseB3 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB3 (i : Fin 200) : Certificate (caseB3 i) := by
  refine ⟨lookupB3 i.val,?_,sizeB3 i⟩
  have hv := tableB3_valid i
  rw [funext (srcB3_row i),funext (dstB3_row i)] at hv
  exact hv
lemma certificateInterval3 : FiniteIntervals.Covers CertificateAt 600 800 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 600 200 (fun i _ => certificateB3 i)
#print axioms certificateInterval3
end Erdos184Work.FiveRows3

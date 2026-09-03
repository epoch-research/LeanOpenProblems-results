import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src600 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst600 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle600_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle600_1 : CycleData E W := ⟨4,![3,11,12,13,8,7],![3,4,26,5,14,16]⟩
def cycle600_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle600_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle600_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle600_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data600 : PartitionData E W := ⟨6,![cycle600_0,cycle600_1,cycle600_2,cycle600_3,cycle600_4,cycle600_5]⟩
lemma valid_data600 : data600.Valid src600 dst600 Finset.univ := by decide +kernel

def src601 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,38,26,16,39,8,28,38,18,39]
def dst601 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle601_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle601_1 : CycleData E W := ⟨2,![3,11,18,7],![3,4,26,16]⟩
def cycle601_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle601_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle601_4 : CycleData E W := ⟨3,![21,14,8,19,25],![8,28,14,16,39]⟩
def cycle601_5 : CycleData E W := ⟨3,![12,17,23,9,13],![5,26,38,18,14]⟩
def data601 : PartitionData E W := ⟨6,![cycle601_0,cycle601_1,cycle601_2,cycle601_3,cycle601_4,cycle601_5]⟩
lemma valid_data601 : data601.Valid src601 dst601 Finset.univ := by decide +kernel

def src602 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,38,26,16,39,8,28,39,18,38]
def dst602 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle602_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle602_1 : CycleData E W := ⟨2,![3,11,18,7],![3,4,26,16]⟩
def cycle602_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle602_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle602_4 : CycleData E W := ⟨2,![8,19,23,9],![14,16,39,18]⟩
def cycle602_5 : CycleData E W := ⟨4,![12,17,25,21,14,13],![5,26,38,8,28,14]⟩
def data602 : PartitionData E W := ⟨6,![cycle602_0,cycle602_1,cycle602_2,cycle602_3,cycle602_4,cycle602_5]⟩
lemma valid_data602 : data602.Valid src602 dst602 Finset.univ := by decide +kernel

def src603 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst603 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle603_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle603_1 : CycleData E W := ⟨4,![3,11,12,13,8,7],![3,4,26,5,14,16]⟩
def cycle603_2 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle603_3 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle603_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle603_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data603 : PartitionData E W := ⟨6,![cycle603_0,cycle603_1,cycle603_2,cycle603_3,cycle603_4,cycle603_5]⟩
lemma valid_data603 : data603.Valid src603 dst603 Finset.univ := by decide +kernel

def src604 : E → W := ![2,5,8,3,4,6,2,14,3,16,18,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst604 : E → W := ![5,8,3,4,6,2,14,3,16,18,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle604_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle604_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,8,5,26,14]⟩
def cycle604_2 : CycleData E W := ⟨3,![3,15,22,17,8],![3,4,28,38,16]⟩
def cycle604_3 : CycleData E W := ⟨2,![6,14,23,10],![2,14,28,18]⟩
def cycle604_4 : CycleData E W := ⟨2,![9,24,19,18],![16,18,39,26]⟩
def cycle604_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data604 : PartitionData E W := ⟨6,![cycle604_0,cycle604_1,cycle604_2,cycle604_3,cycle604_4,cycle604_5]⟩
lemma valid_data604 : data604.Valid src604 dst604 Finset.univ := by decide +kernel

def src605 : E → W := ![2,5,8,3,4,6,2,14,3,16,18,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst605 : E → W := ![5,8,3,4,6,2,14,3,16,18,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle605_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle605_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,8,5,26,14]⟩
def cycle605_2 : CycleData E W := ⟨3,![3,15,24,19,8],![3,4,28,39,16]⟩
def cycle605_3 : CycleData E W := ⟨2,![6,14,23,10],![2,14,28,18]⟩
def cycle605_4 : CycleData E W := ⟨2,![9,22,17,18],![16,18,38,26]⟩
def cycle605_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data605 : PartitionData E W := ⟨6,![cycle605_0,cycle605_1,cycle605_2,cycle605_3,cycle605_4,cycle605_5]⟩
lemma valid_data605 : data605.Valid src605 dst605 Finset.univ := by decide +kernel

def src606 : E → W := ![2,5,8,3,4,6,2,14,3,18,16,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst606 : E → W := ![5,8,3,4,6,2,14,3,18,16,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle606_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle606_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,8,5,26,14]⟩
def cycle606_2 : CycleData E W := ⟨2,![3,15,23,8],![3,4,28,18]⟩
def cycle606_3 : CycleData E W := ⟨3,![6,14,22,17,10],![2,14,28,38,16]⟩
def cycle606_4 : CycleData E W := ⟨2,![9,24,19,18],![16,18,39,26]⟩
def cycle606_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data606 : PartitionData E W := ⟨6,![cycle606_0,cycle606_1,cycle606_2,cycle606_3,cycle606_4,cycle606_5]⟩
lemma valid_data606 : data606.Valid src606 dst606 Finset.univ := by decide +kernel

def src607 : E → W := ![2,5,8,3,4,6,2,14,3,18,16,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst607 : E → W := ![5,8,3,4,6,2,14,3,18,16,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle607_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle607_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,8,5,26,14]⟩
def cycle607_2 : CycleData E W := ⟨2,![3,15,23,8],![3,4,28,18]⟩
def cycle607_3 : CycleData E W := ⟨3,![6,14,24,19,10],![2,14,28,39,16]⟩
def cycle607_4 : CycleData E W := ⟨2,![9,22,17,18],![16,18,38,26]⟩
def cycle607_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data607 : PartitionData E W := ⟨6,![cycle607_0,cycle607_1,cycle607_2,cycle607_3,cycle607_4,cycle607_5]⟩
lemma valid_data607 : data607.Valid src607 dst607 Finset.univ := by decide +kernel

def src608 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,16,38,26,39,8,38,18,28,39]
def dst608 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle608_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle608_1 : CycleData E W := ⟨2,![1,21,18,12],![5,8,38,26]⟩
def cycle608_2 : CycleData E W := ⟨3,![2,25,20,16,8],![3,8,39,6,16]⟩
def cycle608_3 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle608_4 : CycleData E W := ⟨3,![6,7,17,22,10],![2,14,16,38,18]⟩
def cycle608_5 : CycleData E W := ⟨2,![13,19,24,14],![14,26,39,28]⟩
def data608 : PartitionData E W := ⟨6,![cycle608_0,cycle608_1,cycle608_2,cycle608_3,cycle608_4,cycle608_5]⟩
lemma valid_data608 : data608.Valid src608 dst608 Finset.univ := by decide +kernel

def src609 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,16,38,26,39,8,38,28,18,39]
def dst609 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle609_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle609_1 : CycleData E W := ⟨2,![1,21,18,12],![5,8,38,26]⟩
def cycle609_2 : CycleData E W := ⟨3,![2,25,20,16,8],![3,8,39,6,16]⟩
def cycle609_3 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle609_4 : CycleData E W := ⟨3,![6,13,19,24,10],![2,14,26,39,18]⟩
def cycle609_5 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def data609 : PartitionData E W := ⟨6,![cycle609_0,cycle609_1,cycle609_2,cycle609_3,cycle609_4,cycle609_5]⟩
lemma valid_data609 : data609.Valid src609 dst609 Finset.univ := by decide +kernel

def src610 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,16,39,26,38,8,38,18,28,39]
def dst610 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle610_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle610_1 : CycleData E W := ⟨2,![1,21,19,12],![5,8,38,26]⟩
def cycle610_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,39,16]⟩
def cycle610_3 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle610_4 : CycleData E W := ⟨4,![6,7,16,20,22,10],![2,14,16,6,38,18]⟩
def cycle610_5 : CycleData E W := ⟨2,![13,18,24,14],![14,26,39,28]⟩
def data610 : PartitionData E W := ⟨6,![cycle610_0,cycle610_1,cycle610_2,cycle610_3,cycle610_4,cycle610_5]⟩
lemma valid_data610 : data610.Valid src610 dst610 Finset.univ := by decide +kernel

def src611 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,16,39,26,38,8,38,28,18,39]
def dst611 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle611_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle611_1 : CycleData E W := ⟨2,![1,21,19,12],![5,8,38,26]⟩
def cycle611_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,39,16]⟩
def cycle611_3 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle611_4 : CycleData E W := ⟨3,![6,13,18,24,10],![2,14,26,39,18]⟩
def cycle611_5 : CycleData E W := ⟨3,![16,7,14,22,20],![6,16,14,28,38]⟩
def data611 : PartitionData E W := ⟨6,![cycle611_0,cycle611_1,cycle611_2,cycle611_3,cycle611_4,cycle611_5]⟩
lemma valid_data611 : data611.Valid src611 dst611 Finset.univ := by decide +kernel

def src612 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,38,16,26,39,8,18,38,28,39]
def dst612 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle612_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle612_1 : CycleData E W := ⟨2,![1,25,19,12],![5,8,39,26]⟩
def cycle612_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle612_3 : CycleData E W := ⟨3,![3,15,14,7,8],![3,4,28,14,16]⟩
def cycle612_4 : CycleData E W := ⟨4,![6,13,18,17,22,10],![2,14,26,16,38,18]⟩
def cycle612_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data612 : PartitionData E W := ⟨6,![cycle612_0,cycle612_1,cycle612_2,cycle612_3,cycle612_4,cycle612_5]⟩
lemma valid_data612 : data612.Valid src612 dst612 Finset.univ := by decide +kernel

def src613 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,38,16,26,39,8,18,39,28,38]
def dst613 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle613_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle613_1 : CycleData E W := ⟨3,![1,21,22,19,12],![5,8,18,39,26]⟩
def cycle613_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,38,16]⟩
def cycle613_3 : CycleData E W := ⟨4,![6,14,15,3,9,10],![2,14,28,4,3,18]⟩
def cycle613_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle613_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data613 : PartitionData E W := ⟨6,![cycle613_0,cycle613_1,cycle613_2,cycle613_3,cycle613_4,cycle613_5]⟩
lemma valid_data613 : data613.Valid src613 dst613 Finset.univ := by decide +kernel

def src614 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst614 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle614_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle614_1 : CycleData E W := ⟨3,![2,1,12,18,8],![3,8,5,26,16]⟩
def cycle614_2 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle614_3 : CycleData E W := ⟨3,![6,13,19,24,10],![2,14,26,39,18]⟩
def cycle614_4 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle614_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data614 : PartitionData E W := ⟨6,![cycle614_0,cycle614_1,cycle614_2,cycle614_3,cycle614_4,cycle614_5]⟩
lemma valid_data614 : data614.Valid src614 dst614 Finset.univ := by decide +kernel

def src615 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,38,26,16,39,8,18,38,28,39]
def dst615 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle615_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle615_1 : CycleData E W := ⟨3,![1,21,22,17,12],![5,8,18,38,26]⟩
def cycle615_2 : CycleData E W := ⟨2,![2,25,19,8],![3,8,39,16]⟩
def cycle615_3 : CycleData E W := ⟨4,![6,14,15,3,9,10],![2,14,28,4,3,18]⟩
def cycle615_4 : CycleData E W := ⟨1,![7,18,13],![14,16,26]⟩
def cycle615_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data615 : PartitionData E W := ⟨6,![cycle615_0,cycle615_1,cycle615_2,cycle615_3,cycle615_4,cycle615_5]⟩
lemma valid_data615 : data615.Valid src615 dst615 Finset.univ := by decide +kernel

def src616 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,38,26,16,39,8,18,39,28,38]
def dst616 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle616_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle616_1 : CycleData E W := ⟨2,![1,25,17,12],![5,8,38,26]⟩
def cycle616_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle616_3 : CycleData E W := ⟨3,![3,15,14,7,8],![3,4,28,14,16]⟩
def cycle616_4 : CycleData E W := ⟨4,![6,13,18,19,22,10],![2,14,26,16,39,18]⟩
def cycle616_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data616 : PartitionData E W := ⟨6,![cycle616_0,cycle616_1,cycle616_2,cycle616_3,cycle616_4,cycle616_5]⟩
lemma valid_data616 : data616.Valid src616 dst616 Finset.univ := by decide +kernel

def src617 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst617 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle617_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle617_1 : CycleData E W := ⟨3,![2,1,12,18,8],![3,8,5,26,16]⟩
def cycle617_2 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle617_3 : CycleData E W := ⟨3,![6,13,17,22,10],![2,14,26,38,18]⟩
def cycle617_4 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle617_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data617 : PartitionData E W := ⟨6,![cycle617_0,cycle617_1,cycle617_2,cycle617_3,cycle617_4,cycle617_5]⟩
lemma valid_data617 : data617.Valid src617 dst617 Finset.univ := by decide +kernel

def src618 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,26,38,39,8,38,18,28,39]
def dst618 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,26,38,39,6,38,18,28,39,8]
def cycle618_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,8,3,18]⟩
def cycle618_1 : CycleData E W := ⟨2,![3,4,16,8],![3,4,6,16]⟩
def cycle618_2 : CycleData E W := ⟨3,![5,20,24,14,6],![2,6,39,28,14]⟩
def cycle618_3 : CycleData E W := ⟨2,![12,17,7,13],![5,26,16,14]⟩
def cycle618_4 : CycleData E W := ⟨3,![11,18,22,23,15],![4,26,38,18,28]⟩
def cycle618_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data618 : PartitionData E W := ⟨6,![cycle618_0,cycle618_1,cycle618_2,cycle618_3,cycle618_4,cycle618_5]⟩
lemma valid_data618 : data618.Valid src618 dst618 Finset.univ := by decide +kernel

def src619 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,26,39,38,8,38,28,18,39]
def dst619 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,26,39,38,6,38,28,18,39,8]
def cycle619_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,8,3,18]⟩
def cycle619_1 : CycleData E W := ⟨2,![3,4,16,8],![3,4,6,16]⟩
def cycle619_2 : CycleData E W := ⟨3,![5,20,22,14,6],![2,6,38,28,14]⟩
def cycle619_3 : CycleData E W := ⟨2,![12,17,7,13],![5,26,16,14]⟩
def cycle619_4 : CycleData E W := ⟨3,![11,18,24,23,15],![4,26,39,18,28]⟩
def cycle619_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data619 : PartitionData E W := ⟨6,![cycle619_0,cycle619_1,cycle619_2,cycle619_3,cycle619_4,cycle619_5]⟩
lemma valid_data619 : data619.Valid src619 dst619 Finset.univ := by decide +kernel

def src620 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,38,26,39,8,28,38,18,39]
def dst620 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,38,26,39,6,28,38,18,39,8]
def cycle620_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle620_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle620_2 : CycleData E W := ⟨3,![4,16,7,14,15],![4,6,16,14,28]⟩
def cycle620_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle620_4 : CycleData E W := ⟨2,![8,17,23,9],![3,16,38,18]⟩
def cycle620_5 : CycleData E W := ⟨3,![21,22,18,19,25],![8,28,38,26,39]⟩
def data620 : PartitionData E W := ⟨6,![cycle620_0,cycle620_1,cycle620_2,cycle620_3,cycle620_4,cycle620_5]⟩
lemma valid_data620 : data620.Valid src620 dst620 Finset.univ := by decide +kernel

def src621 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,38,26,39,8,28,39,18,38]
def dst621 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,38,26,39,6,28,39,18,38,8]
def cycle621_0 : CycleData E W := ⟨4,![0,12,11,3,9,10],![2,5,26,4,3,18]⟩
def cycle621_1 : CycleData E W := ⟨2,![1,21,14,13],![5,8,28,14]⟩
def cycle621_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,38,16]⟩
def cycle621_3 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle621_4 : CycleData E W := ⟨2,![5,16,7,6],![2,6,16,14]⟩
def cycle621_5 : CycleData E W := ⟨2,![23,19,18,24],![18,39,26,38]⟩
def data621 : PartitionData E W := ⟨6,![cycle621_0,cycle621_1,cycle621_2,cycle621_3,cycle621_4,cycle621_5]⟩
lemma valid_data621 : data621.Valid src621 dst621 Finset.univ := by decide +kernel

def src622 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,38,26,39,8,38,18,28,39]
def dst622 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle622_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle622_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle622_2 : CycleData E W := ⟨3,![4,16,7,14,15],![4,6,16,14,28]⟩
def cycle622_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle622_4 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def cycle622_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data622 : PartitionData E W := ⟨6,![cycle622_0,cycle622_1,cycle622_2,cycle622_3,cycle622_4,cycle622_5]⟩
lemma valid_data622 : data622.Valid src622 dst622 Finset.univ := by decide +kernel

def src623 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,38,26,39,8,38,28,18,39]
def dst623 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle623_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle623_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle623_2 : CycleData E W := ⟨3,![4,16,7,14,15],![4,6,16,14,28]⟩
def cycle623_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle623_4 : CycleData E W := ⟨3,![8,17,22,23,9],![3,16,38,28,18]⟩
def cycle623_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data623 : PartitionData E W := ⟨6,![cycle623_0,cycle623_1,cycle623_2,cycle623_3,cycle623_4,cycle623_5]⟩
lemma valid_data623 : data623.Valid src623 dst623 Finset.univ := by decide +kernel

def src624 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,38,39,26,8,38,28,18,39]
def dst624 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,38,39,26,6,38,28,18,39,8]
def cycle624_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,8,3,18]⟩
def cycle624_1 : CycleData E W := ⟨2,![3,4,16,8],![3,4,6,16]⟩
def cycle624_2 : CycleData E W := ⟨3,![5,20,12,13,6],![2,6,26,5,14]⟩
def cycle624_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle624_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle624_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data624 : PartitionData E W := ⟨6,![cycle624_0,cycle624_1,cycle624_2,cycle624_3,cycle624_4,cycle624_5]⟩
lemma valid_data624 : data624.Valid src624 dst624 Finset.univ := by decide +kernel

def src625 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,39,26,38,8,28,38,18,39]
def dst625 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,39,26,38,6,28,38,18,39,8]
def cycle625_0 : CycleData E W := ⟨4,![0,12,11,3,9,10],![2,5,26,4,3,18]⟩
def cycle625_1 : CycleData E W := ⟨2,![1,21,14,13],![5,8,28,14]⟩
def cycle625_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,39,16]⟩
def cycle625_3 : CycleData E W := ⟨2,![4,20,22,15],![4,6,38,28]⟩
def cycle625_4 : CycleData E W := ⟨2,![5,16,7,6],![2,6,16,14]⟩
def cycle625_5 : CycleData E W := ⟨2,![23,19,18,24],![18,38,26,39]⟩
def data625 : PartitionData E W := ⟨6,![cycle625_0,cycle625_1,cycle625_2,cycle625_3,cycle625_4,cycle625_5]⟩
lemma valid_data625 : data625.Valid src625 dst625 Finset.univ := by decide +kernel

def src626 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,39,26,38,8,28,39,18,38]
def dst626 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,39,26,38,6,28,39,18,38,8]
def cycle626_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle626_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle626_2 : CycleData E W := ⟨3,![4,16,7,14,15],![4,6,16,14,28]⟩
def cycle626_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,38,18]⟩
def cycle626_4 : CycleData E W := ⟨2,![8,17,23,9],![3,16,39,18]⟩
def cycle626_5 : CycleData E W := ⟨3,![21,22,18,19,25],![8,28,39,26,38]⟩
def data626 : PartitionData E W := ⟨6,![cycle626_0,cycle626_1,cycle626_2,cycle626_3,cycle626_4,cycle626_5]⟩
lemma valid_data626 : data626.Valid src626 dst626 Finset.univ := by decide +kernel

def src627 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,39,26,38,8,38,18,28,39]
def dst627 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle627_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle627_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle627_2 : CycleData E W := ⟨3,![4,16,7,14,15],![4,6,16,14,28]⟩
def cycle627_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle627_4 : CycleData E W := ⟨3,![8,17,24,23,9],![3,16,39,28,18]⟩
def cycle627_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data627 : PartitionData E W := ⟨6,![cycle627_0,cycle627_1,cycle627_2,cycle627_3,cycle627_4,cycle627_5]⟩
lemma valid_data627 : data627.Valid src627 dst627 Finset.univ := by decide +kernel

def src628 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,39,26,38,8,38,28,18,39]
def dst628 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle628_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle628_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle628_2 : CycleData E W := ⟨3,![4,16,7,14,15],![4,6,16,14,28]⟩
def cycle628_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle628_4 : CycleData E W := ⟨2,![8,17,24,9],![3,16,39,18]⟩
def cycle628_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data628 : PartitionData E W := ⟨6,![cycle628_0,cycle628_1,cycle628_2,cycle628_3,cycle628_4,cycle628_5]⟩
lemma valid_data628 : data628.Valid src628 dst628 Finset.univ := by decide +kernel

def src629 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,16,39,38,26,8,38,18,28,39]
def dst629 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,16,39,38,26,6,38,18,28,39,8]
def cycle629_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,8,3,18]⟩
def cycle629_1 : CycleData E W := ⟨2,![3,4,16,8],![3,4,6,16]⟩
def cycle629_2 : CycleData E W := ⟨3,![5,20,12,13,6],![2,6,26,5,14]⟩
def cycle629_3 : CycleData E W := ⟨2,![7,17,24,14],![14,16,39,28]⟩
def cycle629_4 : CycleData E W := ⟨3,![11,19,22,23,15],![4,26,38,18,28]⟩
def cycle629_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data629 : PartitionData E W := ⟨6,![cycle629_0,cycle629_1,cycle629_2,cycle629_3,cycle629_4,cycle629_5]⟩
lemma valid_data629 : data629.Valid src629 dst629 Finset.univ := by decide +kernel

def src630 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,16,38,39,8,38,28,18,39]
def dst630 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,16,38,39,6,38,28,18,39,8]
def cycle630_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle630_1 : CycleData E W := ⟨3,![2,1,12,17,8],![3,8,5,26,16]⟩
def cycle630_2 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle630_3 : CycleData E W := ⟨1,![4,16,11],![4,6,26]⟩
def cycle630_4 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle630_5 : CycleData E W := ⟨2,![7,18,22,14],![14,16,38,28]⟩
def cycle630_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data630 : PartitionData E W := ⟨7,![cycle630_0,cycle630_1,cycle630_2,cycle630_3,cycle630_4,cycle630_5,cycle630_6]⟩
lemma valid_data630 : data630.Valid src630 dst630 Finset.univ := by decide +kernel

def src631 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,16,39,38,8,38,18,28,39]
def dst631 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,16,39,38,6,38,18,28,39,8]
def cycle631_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle631_1 : CycleData E W := ⟨3,![2,1,12,17,8],![3,8,5,26,16]⟩
def cycle631_2 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle631_3 : CycleData E W := ⟨1,![4,16,11],![4,6,26]⟩
def cycle631_4 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle631_5 : CycleData E W := ⟨2,![7,18,24,14],![14,16,39,28]⟩
def cycle631_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data631 : PartitionData E W := ⟨7,![cycle631_0,cycle631_1,cycle631_2,cycle631_3,cycle631_4,cycle631_5,cycle631_6]⟩
lemma valid_data631 : data631.Valid src631 dst631 Finset.univ := by decide +kernel

def src632 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,38,16,39,8,18,38,28,39]
def dst632 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,38,16,39,6,18,38,28,39,8]
def cycle632_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle632_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle632_2 : CycleData E W := ⟨3,![4,16,17,23,15],![4,6,26,38,28]⟩
def cycle632_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle632_4 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle632_5 : CycleData E W := ⟨2,![8,18,22,9],![3,16,38,18]⟩
def data632 : PartitionData E W := ⟨6,![cycle632_0,cycle632_1,cycle632_2,cycle632_3,cycle632_4,cycle632_5]⟩
lemma valid_data632 : data632.Valid src632 dst632 Finset.univ := by decide +kernel

def src633 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,38,16,39,8,18,39,28,38]
def dst633 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,38,16,39,6,18,39,28,38,8]
def cycle633_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle633_1 : CycleData E W := ⟨2,![1,25,17,12],![5,8,38,26]⟩
def cycle633_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle633_3 : CycleData E W := ⟨3,![3,15,14,7,8],![3,4,28,14,16]⟩
def cycle633_4 : CycleData E W := ⟨1,![4,16,11],![4,6,26]⟩
def cycle633_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle633_6 : CycleData E W := ⟨2,![18,24,23,19],![16,38,28,39]⟩
def data633 : PartitionData E W := ⟨7,![cycle633_0,cycle633_1,cycle633_2,cycle633_3,cycle633_4,cycle633_5,cycle633_6]⟩
lemma valid_data633 : data633.Valid src633 dst633 Finset.univ := by decide +kernel

def src634 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,38,16,39,8,38,18,28,39]
def dst634 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle634_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle634_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle634_2 : CycleData E W := ⟨3,![5,4,15,23,10],![2,6,4,28,18]⟩
def cycle634_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle634_4 : CycleData E W := ⟨2,![8,18,22,9],![3,16,38,18]⟩
def cycle634_5 : CycleData E W := ⟨3,![16,17,21,25,20],![6,26,38,8,39]⟩
def data634 : PartitionData E W := ⟨6,![cycle634_0,cycle634_1,cycle634_2,cycle634_3,cycle634_4,cycle634_5]⟩
lemma valid_data634 : data634.Valid src634 dst634 Finset.univ := by decide +kernel

def src635 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,38,16,39,8,38,28,18,39]
def dst635 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle635_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle635_1 : CycleData E W := ⟨2,![1,21,17,12],![5,8,38,26]⟩
def cycle635_2 : CycleData E W := ⟨2,![2,25,19,8],![3,8,39,16]⟩
def cycle635_3 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle635_4 : CycleData E W := ⟨1,![4,16,11],![4,6,26]⟩
def cycle635_5 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle635_6 : CycleData E W := ⟨2,![7,18,22,14],![14,16,38,28]⟩
def data635 : PartitionData E W := ⟨7,![cycle635_0,cycle635_1,cycle635_2,cycle635_3,cycle635_4,cycle635_5,cycle635_6]⟩
lemma valid_data635 : data635.Valid src635 dst635 Finset.univ := by decide +kernel

def src636 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,39,16,38,8,18,38,28,39]
def dst636 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,39,16,38,6,18,38,28,39,8]
def cycle636_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle636_1 : CycleData E W := ⟨2,![1,25,17,12],![5,8,39,26]⟩
def cycle636_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle636_3 : CycleData E W := ⟨3,![3,15,14,7,8],![3,4,28,14,16]⟩
def cycle636_4 : CycleData E W := ⟨1,![4,16,11],![4,6,26]⟩
def cycle636_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle636_6 : CycleData E W := ⟨2,![18,24,23,19],![16,39,28,38]⟩
def data636 : PartitionData E W := ⟨7,![cycle636_0,cycle636_1,cycle636_2,cycle636_3,cycle636_4,cycle636_5,cycle636_6]⟩
lemma valid_data636 : data636.Valid src636 dst636 Finset.univ := by decide +kernel

def src637 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,39,16,38,8,18,39,28,38]
def dst637 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,39,16,38,6,18,39,28,38,8]
def cycle637_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle637_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle637_2 : CycleData E W := ⟨3,![4,16,17,23,15],![4,6,26,39,28]⟩
def cycle637_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,38,8,18]⟩
def cycle637_4 : CycleData E W := ⟨2,![7,19,24,14],![14,16,38,28]⟩
def cycle637_5 : CycleData E W := ⟨2,![8,18,22,9],![3,16,39,18]⟩
def data637 : PartitionData E W := ⟨6,![cycle637_0,cycle637_1,cycle637_2,cycle637_3,cycle637_4,cycle637_5]⟩
lemma valid_data637 : data637.Valid src637 dst637 Finset.univ := by decide +kernel

def src638 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,39,16,38,8,38,18,28,39]
def dst638 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle638_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle638_1 : CycleData E W := ⟨2,![1,25,17,12],![5,8,39,26]⟩
def cycle638_2 : CycleData E W := ⟨2,![2,21,19,8],![3,8,38,16]⟩
def cycle638_3 : CycleData E W := ⟨2,![3,15,23,9],![3,4,28,18]⟩
def cycle638_4 : CycleData E W := ⟨1,![4,16,11],![4,6,26]⟩
def cycle638_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle638_6 : CycleData E W := ⟨2,![7,18,24,14],![14,16,39,28]⟩
def data638 : PartitionData E W := ⟨7,![cycle638_0,cycle638_1,cycle638_2,cycle638_3,cycle638_4,cycle638_5,cycle638_6]⟩
lemma valid_data638 : data638.Valid src638 dst638 Finset.univ := by decide +kernel

def src639 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,26,39,16,38,8,38,28,18,39]
def dst639 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle639_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle639_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle639_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,38,28]⟩
def cycle639_3 : CycleData E W := ⟨3,![5,16,17,24,10],![2,6,26,39,18]⟩
def cycle639_4 : CycleData E W := ⟨3,![8,7,14,23,9],![3,16,14,28,18]⟩
def cycle639_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data639 : PartitionData E W := ⟨6,![cycle639_0,cycle639_1,cycle639_2,cycle639_3,cycle639_4,cycle639_5]⟩
lemma valid_data639 : data639.Valid src639 dst639 Finset.univ := by decide +kernel

def src640 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,18,28,38,39]
def dst640 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,18,28,38,39,8]
def cycle640_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle640_1 : CycleData E W := ⟨2,![1,25,19,12],![5,8,39,26]⟩
def cycle640_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle640_3 : CycleData E W := ⟨2,![3,11,18,8],![3,4,26,16]⟩
def cycle640_4 : CycleData E W := ⟨3,![5,4,15,22,10],![2,6,4,28,18]⟩
def cycle640_5 : CycleData E W := ⟨2,![7,17,23,14],![14,16,38,28]⟩
def cycle640_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data640 : PartitionData E W := ⟨7,![cycle640_0,cycle640_1,cycle640_2,cycle640_3,cycle640_4,cycle640_5,cycle640_6]⟩
lemma valid_data640 : data640.Valid src640 dst640 Finset.univ := by decide +kernel

def src641 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,18,38,28,39]
def dst641 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle641_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle641_1 : CycleData E W := ⟨2,![1,25,19,12],![5,8,39,26]⟩
def cycle641_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle641_3 : CycleData E W := ⟨2,![3,11,18,8],![3,4,26,16]⟩
def cycle641_4 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle641_5 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle641_6 : CycleData E W := ⟨2,![7,17,23,14],![14,16,38,28]⟩
def data641 : PartitionData E W := ⟨7,![cycle641_0,cycle641_1,cycle641_2,cycle641_3,cycle641_4,cycle641_5,cycle641_6]⟩
lemma valid_data641 : data641.Valid src641 dst641 Finset.univ := by decide +kernel

def src642 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,18,39,28,38]
def dst642 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle642_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle642_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle642_2 : CycleData E W := ⟨2,![4,20,23,15],![4,6,39,28]⟩
def cycle642_3 : CycleData E W := ⟨3,![5,16,25,21,10],![2,6,38,8,18]⟩
def cycle642_4 : CycleData E W := ⟨2,![7,17,24,14],![14,16,38,28]⟩
def cycle642_5 : CycleData E W := ⟨3,![8,18,19,22,9],![3,16,26,39,18]⟩
def data642 : PartitionData E W := ⟨6,![cycle642_0,cycle642_1,cycle642_2,cycle642_3,cycle642_4,cycle642_5]⟩
lemma valid_data642 : data642.Valid src642 dst642 Finset.univ := by decide +kernel

def src643 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,18,39,38,28]
def dst643 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,18,39,38,28,8]
def cycle643_0 : CycleData E W := ⟨3,![0,12,11,4,5],![2,5,26,4,6]⟩
def cycle643_1 : CycleData E W := ⟨3,![6,13,1,21,10],![2,14,5,8,18]⟩
def cycle643_2 : CycleData E W := ⟨2,![2,25,15,3],![3,8,28,4]⟩
def cycle643_3 : CycleData E W := ⟨2,![7,17,24,14],![14,16,38,28]⟩
def cycle643_4 : CycleData E W := ⟨3,![8,18,19,22,9],![3,16,26,39,18]⟩
def cycle643_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data643 : PartitionData E W := ⟨6,![cycle643_0,cycle643_1,cycle643_2,cycle643_3,cycle643_4,cycle643_5]⟩
lemma valid_data643 : data643.Valid src643 dst643 Finset.univ := by decide +kernel

def src644 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,28,18,39,38]
def dst644 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,28,18,39,38,8]
def cycle644_0 : CycleData E W := ⟨3,![0,12,11,4,5],![2,5,26,4,6]⟩
def cycle644_1 : CycleData E W := ⟨2,![1,21,14,13],![5,8,28,14]⟩
def cycle644_2 : CycleData E W := ⟨2,![2,25,17,8],![3,8,38,16]⟩
def cycle644_3 : CycleData E W := ⟨2,![3,15,22,9],![3,4,28,18]⟩
def cycle644_4 : CycleData E W := ⟨4,![6,7,18,19,23,10],![2,14,16,26,39,18]⟩
def cycle644_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data644 : PartitionData E W := ⟨6,![cycle644_0,cycle644_1,cycle644_2,cycle644_3,cycle644_4,cycle644_5]⟩
lemma valid_data644 : data644.Valid src644 dst644 Finset.univ := by decide +kernel

def src645 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,28,38,18,39]
def dst645 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle645_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle645_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle645_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle645_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle645_4 : CycleData E W := ⟨4,![21,14,7,18,19,25],![8,28,14,16,26,39]⟩
def cycle645_5 : CycleData E W := ⟨2,![8,17,23,9],![3,16,38,18]⟩
def data645 : PartitionData E W := ⟨6,![cycle645_0,cycle645_1,cycle645_2,cycle645_3,cycle645_4,cycle645_5]⟩
lemma valid_data645 : data645.Valid src645 dst645 Finset.univ := by decide +kernel

def src646 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,28,39,18,38]
def dst646 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle646_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle646_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle646_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle646_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle646_4 : CycleData E W := ⟨3,![21,14,7,17,25],![8,28,14,16,38]⟩
def cycle646_5 : CycleData E W := ⟨3,![8,18,19,23,9],![3,16,26,39,18]⟩
def data646 : PartitionData E W := ⟨6,![cycle646_0,cycle646_1,cycle646_2,cycle646_3,cycle646_4,cycle646_5]⟩
lemma valid_data646 : data646.Valid src646 dst646 Finset.univ := by decide +kernel

def src647 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst647 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle647_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle647_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle647_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle647_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle647_4 : CycleData E W := ⟨3,![8,7,14,23,9],![3,16,14,28,18]⟩
def cycle647_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data647 : PartitionData E W := ⟨6,![cycle647_0,cycle647_1,cycle647_2,cycle647_3,cycle647_4,cycle647_5]⟩
lemma valid_data647 : data647.Valid src647 dst647 Finset.univ := by decide +kernel

def src648 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,18,28,39,38]
def dst648 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,18,28,39,38,8]
def cycle648_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle648_1 : CycleData E W := ⟨2,![1,25,17,12],![5,8,38,26]⟩
def cycle648_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle648_3 : CycleData E W := ⟨2,![3,11,18,8],![3,4,26,16]⟩
def cycle648_4 : CycleData E W := ⟨3,![5,4,15,22,10],![2,6,4,28,18]⟩
def cycle648_5 : CycleData E W := ⟨2,![7,19,23,14],![14,16,39,28]⟩
def cycle648_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data648 : PartitionData E W := ⟨7,![cycle648_0,cycle648_1,cycle648_2,cycle648_3,cycle648_4,cycle648_5,cycle648_6]⟩
lemma valid_data648 : data648.Valid src648 dst648 Finset.univ := by decide +kernel

def src649 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,18,38,28,39]
def dst649 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle649_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle649_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle649_2 : CycleData E W := ⟨2,![4,16,23,15],![4,6,38,28]⟩
def cycle649_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle649_4 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle649_5 : CycleData E W := ⟨3,![8,18,17,22,9],![3,16,26,38,18]⟩
def data649 : PartitionData E W := ⟨6,![cycle649_0,cycle649_1,cycle649_2,cycle649_3,cycle649_4,cycle649_5]⟩
lemma valid_data649 : data649.Valid src649 dst649 Finset.univ := by decide +kernel

def lookupB12 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data600 else (if j < 2 then data601 else data602)) else (if j < 4 then data603 else (if j < 5 then data604 else data605))) else (if j < 9 then (if j < 7 then data606 else (if j < 8 then data607 else data608)) else (if j < 10 then data609 else (if j < 11 then data610 else data611)))) else (if j < 18 then (if j < 15 then (if j < 13 then data612 else (if j < 14 then data613 else data614)) else (if j < 16 then data615 else (if j < 17 then data616 else data617))) else (if j < 21 then (if j < 19 then data618 else (if j < 20 then data619 else data620)) else (if j < 23 then (if j < 22 then data621 else data622) else (if j < 24 then data623 else data624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data625 else (if j < 27 then data626 else data627)) else (if j < 29 then data628 else (if j < 30 then data629 else data630))) else (if j < 34 then (if j < 32 then data631 else (if j < 33 then data632 else data633)) else (if j < 35 then data634 else (if j < 36 then data635 else data636)))) else (if j < 43 then (if j < 40 then (if j < 38 then data637 else (if j < 39 then data638 else data639)) else (if j < 41 then data640 else (if j < 42 then data641 else data642))) else (if j < 46 then (if j < 44 then data643 else (if j < 45 then data644 else data645)) else (if j < 48 then (if j < 47 then data646 else data647) else (if j < 49 then data648 else data649))))))

def srcTableB12 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src600 else (if j < 2 then src601 else src602)) else (if j < 4 then src603 else (if j < 5 then src604 else src605))) else (if j < 9 then (if j < 7 then src606 else (if j < 8 then src607 else src608)) else (if j < 10 then src609 else (if j < 11 then src610 else src611)))) else (if j < 18 then (if j < 15 then (if j < 13 then src612 else (if j < 14 then src613 else src614)) else (if j < 16 then src615 else (if j < 17 then src616 else src617))) else (if j < 21 then (if j < 19 then src618 else (if j < 20 then src619 else src620)) else (if j < 23 then (if j < 22 then src621 else src622) else (if j < 24 then src623 else src624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src625 else (if j < 27 then src626 else src627)) else (if j < 29 then src628 else (if j < 30 then src629 else src630))) else (if j < 34 then (if j < 32 then src631 else (if j < 33 then src632 else src633)) else (if j < 35 then src634 else (if j < 36 then src635 else src636)))) else (if j < 43 then (if j < 40 then (if j < 38 then src637 else (if j < 39 then src638 else src639)) else (if j < 41 then src640 else (if j < 42 then src641 else src642))) else (if j < 46 then (if j < 44 then src643 else (if j < 45 then src644 else src645)) else (if j < 48 then (if j < 47 then src646 else src647) else (if j < 49 then src648 else src649))))))

def dstTableB12 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst600 else (if j < 2 then dst601 else dst602)) else (if j < 4 then dst603 else (if j < 5 then dst604 else dst605))) else (if j < 9 then (if j < 7 then dst606 else (if j < 8 then dst607 else dst608)) else (if j < 10 then dst609 else (if j < 11 then dst610 else dst611)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst612 else (if j < 14 then dst613 else dst614)) else (if j < 16 then dst615 else (if j < 17 then dst616 else dst617))) else (if j < 21 then (if j < 19 then dst618 else (if j < 20 then dst619 else dst620)) else (if j < 23 then (if j < 22 then dst621 else dst622) else (if j < 24 then dst623 else dst624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst625 else (if j < 27 then dst626 else dst627)) else (if j < 29 then dst628 else (if j < 30 then dst629 else dst630))) else (if j < 34 then (if j < 32 then dst631 else (if j < 33 then dst632 else dst633)) else (if j < 35 then dst634 else (if j < 36 then dst635 else dst636)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst637 else (if j < 39 then dst638 else dst639)) else (if j < 41 then dst640 else (if j < 42 then dst641 else dst642))) else (if j < 46 then (if j < 44 then dst643 else (if j < 45 then dst644 else dst645)) else (if j < 48 then (if j < 47 then dst646 else dst647) else (if j < 49 then dst648 else dst649))))))

def caseB12 (i : Fin 50) : Cases := ⟨600 + i.val,by have := i.isLt; omega⟩
lemma tableB12_valid (i : Fin 50) :
    (lookupB12 i.val).Valid (srcTableB12 i.val) (dstTableB12 i.val) Finset.univ := by
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

lemma srcB12_row : ∀ (i : Fin 50) (e : E),
    srcTableB12 i.val e = caseSource (caseB12 i) e := by decide +kernel

lemma dstB12_row : ∀ (i : Fin 50) (e : E),
    dstTableB12 i.val e = caseTarget (caseB12 i) e := by decide +kernel

lemma sizeB12 : ∀ i : Fin 50, (lookupB12 i.val).size ≤ 5 →
    (lookupB12 i.val).size = 2 ∧
      (⟨caseKey (caseB12 i),caseKey_lt (caseB12 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB12 (i : Fin 50) : Certificate (caseB12 i) := by
  refine ⟨lookupB12 i.val,?_,sizeB12 i⟩
  have hv := tableB12_valid i
  rw [funext (srcB12_row i),funext (dstB12_row i)] at hv
  exact hv
lemma certificateInterval12 : FiniteIntervals.Covers CertificateAt 600 650 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 600 50 (fun i _ => certificateB12 i)
#print axioms certificateInterval12
end Erdos184Work.FiveRows4

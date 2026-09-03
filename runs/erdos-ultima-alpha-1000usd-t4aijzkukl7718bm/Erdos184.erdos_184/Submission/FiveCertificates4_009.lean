import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src450 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,28,39,18,38]
def dst450 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle450_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle450_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle450_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle450_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle450_4 : CycleData E W := ⟨3,![9,23,19,18,12],![14,18,39,16,26]⟩
def cycle450_5 : CycleData E W := ⟨3,![13,17,25,21,14],![5,26,38,8,28]⟩
def data450 : PartitionData E W := ⟨6,![cycle450_0,cycle450_1,cycle450_2,cycle450_3,cycle450_4,cycle450_5]⟩
lemma valid_data450 : data450.Valid src450 dst450 Finset.univ := by decide +kernel

def src451 : E → W := ![2,5,3,8,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst451 : E → W := ![5,3,8,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle451_0 : CycleData E W := ⟨2,![0,1,7,6],![2,5,3,16]⟩
def cycle451_1 : CycleData E W := ⟨2,![2,3,11,8],![3,8,4,14]⟩
def cycle451_2 : CycleData E W := ⟨3,![5,4,15,23,10],![2,6,4,28,18]⟩
def cycle451_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle451_4 : CycleData E W := ⟨3,![13,18,19,24,14],![5,26,16,39,28]⟩
def cycle451_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data451 : PartitionData E W := ⟨6,![cycle451_0,cycle451_1,cycle451_2,cycle451_3,cycle451_4,cycle451_5]⟩
lemma valid_data451 : data451.Valid src451 dst451 Finset.univ := by decide +kernel

def src452 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst452 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle452_0 : CycleData E W := ⟨2,![0,11,3,6],![2,5,4,3]⟩
def cycle452_1 : CycleData E W := ⟨2,![1,16,22,12],![5,6,38,28]⟩
def cycle452_2 : CycleData E W := ⟨2,![2,20,24,7],![3,6,39,18]⟩
def cycle452_3 : CycleData E W := ⟨2,![4,25,19,15],![4,8,39,26]⟩
def cycle452_4 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle452_5 : CycleData E W := ⟨1,![8,23,13],![14,18,28]⟩
def cycle452_6 : CycleData E W := ⟨1,![9,18,14],![14,16,26]⟩
def data452 : PartitionData E W := ⟨7,![cycle452_0,cycle452_1,cycle452_2,cycle452_3,cycle452_4,cycle452_5,cycle452_6]⟩
lemma valid_data452 : data452.Valid src452 dst452 Finset.univ := by decide +kernel

def src453 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst453 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle453_0 : CycleData E W := ⟨2,![0,11,3,6],![2,5,4,3]⟩
def cycle453_1 : CycleData E W := ⟨2,![1,20,24,12],![5,6,39,28]⟩
def cycle453_2 : CycleData E W := ⟨2,![2,16,22,7],![3,6,38,18]⟩
def cycle453_3 : CycleData E W := ⟨2,![4,21,17,15],![4,8,38,26]⟩
def cycle453_4 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle453_5 : CycleData E W := ⟨1,![8,23,13],![14,18,28]⟩
def cycle453_6 : CycleData E W := ⟨1,![9,18,14],![14,16,26]⟩
def data453 : PartitionData E W := ⟨7,![cycle453_0,cycle453_1,cycle453_2,cycle453_3,cycle453_4,cycle453_5,cycle453_6]⟩
lemma valid_data453 : data453.Valid src453 dst453 Finset.univ := by decide +kernel

def src454 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,5,26,28,6,38,16,26,39,8,38,28,18,39]
def dst454 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,5,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle454_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle454_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle454_2 : CycleData E W := ⟨4,![5,4,15,22,17,10],![2,8,4,28,38,16]⟩
def cycle454_3 : CycleData E W := ⟨2,![12,9,18,13],![5,14,16,26]⟩
def cycle454_4 : CycleData E W := ⟨2,![23,14,19,24],![18,28,26,39]⟩
def cycle454_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data454 : PartitionData E W := ⟨6,![cycle454_0,cycle454_1,cycle454_2,cycle454_3,cycle454_4,cycle454_5]⟩
lemma valid_data454 : data454.Valid src454 dst454 Finset.univ := by decide +kernel

def src455 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,5,26,28,6,38,26,16,39,8,38,18,28,39]
def dst455 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,5,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle455_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle455_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle455_2 : CycleData E W := ⟨3,![4,21,17,14,15],![4,8,38,26,28]⟩
def cycle455_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle455_4 : CycleData E W := ⟨2,![12,9,18,13],![5,14,16,26]⟩
def cycle455_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data455 : PartitionData E W := ⟨6,![cycle455_0,cycle455_1,cycle455_2,cycle455_3,cycle455_4,cycle455_5]⟩
lemma valid_data455 : data455.Valid src455 dst455 Finset.univ := by decide +kernel

def src456 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,5,28,26,6,38,16,26,39,8,38,28,18,39]
def dst456 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,5,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle456_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle456_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle456_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle456_3 : CycleData E W := ⟨3,![12,9,17,22,13],![5,14,16,38,28]⟩
def cycle456_4 : CycleData E W := ⟨2,![23,14,19,24],![18,28,26,39]⟩
def cycle456_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data456 : PartitionData E W := ⟨6,![cycle456_0,cycle456_1,cycle456_2,cycle456_3,cycle456_4,cycle456_5]⟩
lemma valid_data456 : data456.Valid src456 dst456 Finset.univ := by decide +kernel

def src457 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,5,28,26,6,38,26,16,39,8,38,18,28,39]
def dst457 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,5,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle457_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle457_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle457_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle457_3 : CycleData E W := ⟨3,![12,9,19,24,13],![5,14,16,39,28]⟩
def cycle457_4 : CycleData E W := ⟨2,![22,17,14,23],![18,38,26,28]⟩
def cycle457_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data457 : PartitionData E W := ⟨6,![cycle457_0,cycle457_1,cycle457_2,cycle457_3,cycle457_4,cycle457_5]⟩
lemma valid_data457 : data457.Valid src457 dst457 Finset.univ := by decide +kernel

def src458 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,26,38,16,39,8,38,18,28,39]
def dst458 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,26,38,16,39,6,38,18,28,39,8]
def cycle458_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle458_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle458_2 : CycleData E W := ⟨2,![4,21,17,15],![4,8,38,26]⟩
def cycle458_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle458_4 : CycleData E W := ⟨3,![9,18,22,23,12],![14,16,38,18,28]⟩
def cycle458_5 : CycleData E W := ⟨3,![13,24,20,16,14],![5,28,39,6,26]⟩
def data458 : PartitionData E W := ⟨6,![cycle458_0,cycle458_1,cycle458_2,cycle458_3,cycle458_4,cycle458_5]⟩
lemma valid_data458 : data458.Valid src458 dst458 Finset.univ := by decide +kernel

def src459 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,26,38,16,39,8,38,28,18,39]
def dst459 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,26,38,16,39,6,38,28,18,39,8]
def cycle459_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle459_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle459_2 : CycleData E W := ⟨2,![4,21,17,15],![4,8,38,26]⟩
def cycle459_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle459_4 : CycleData E W := ⟨2,![9,18,22,12],![14,16,38,28]⟩
def cycle459_5 : CycleData E W := ⟨4,![13,23,24,20,16,14],![5,28,18,39,6,26]⟩
def data459 : PartitionData E W := ⟨6,![cycle459_0,cycle459_1,cycle459_2,cycle459_3,cycle459_4,cycle459_5]⟩
lemma valid_data459 : data459.Valid src459 dst459 Finset.univ := by decide +kernel

def src460 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,26,39,16,38,8,38,18,28,39]
def dst460 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,26,39,16,38,6,38,18,28,39,8]
def cycle460_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle460_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle460_2 : CycleData E W := ⟨3,![4,21,20,16,15],![4,8,38,6,26]⟩
def cycle460_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle460_4 : CycleData E W := ⟨3,![9,19,22,23,12],![14,16,38,18,28]⟩
def cycle460_5 : CycleData E W := ⟨2,![13,24,17,14],![5,28,39,26]⟩
def data460 : PartitionData E W := ⟨6,![cycle460_0,cycle460_1,cycle460_2,cycle460_3,cycle460_4,cycle460_5]⟩
lemma valid_data460 : data460.Valid src460 dst460 Finset.univ := by decide +kernel

def src461 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,26,39,16,38,8,38,28,18,39]
def dst461 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,26,39,16,38,6,38,28,18,39,8]
def cycle461_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle461_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle461_2 : CycleData E W := ⟨3,![4,21,20,16,15],![4,8,38,6,26]⟩
def cycle461_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle461_4 : CycleData E W := ⟨2,![9,19,22,12],![14,16,38,28]⟩
def cycle461_5 : CycleData E W := ⟨3,![13,23,24,17,14],![5,28,18,39,26]⟩
def data461 : PartitionData E W := ⟨6,![cycle461_0,cycle461_1,cycle461_2,cycle461_3,cycle461_4,cycle461_5]⟩
lemma valid_data461 : data461.Valid src461 dst461 Finset.univ := by decide +kernel

def src462 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,38,16,26,39,8,28,38,18,39]
def dst462 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,38,16,26,39,6,28,38,18,39,8]
def cycle462_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle462_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle462_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle462_3 : CycleData E W := ⟨2,![9,17,22,12],![14,16,38,28]⟩
def cycle462_4 : CycleData E W := ⟨3,![13,21,25,19,14],![5,28,8,39,26]⟩
def cycle462_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data462 : PartitionData E W := ⟨6,![cycle462_0,cycle462_1,cycle462_2,cycle462_3,cycle462_4,cycle462_5]⟩
lemma valid_data462 : data462.Valid src462 dst462 Finset.univ := by decide +kernel

def src463 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,38,16,26,39,8,28,39,18,38]
def dst463 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,38,16,26,39,6,28,39,18,38,8]
def cycle463_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle463_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle463_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle463_3 : CycleData E W := ⟨3,![21,12,9,17,25],![8,28,14,16,38]⟩
def cycle463_4 : CycleData E W := ⟨2,![13,22,19,14],![5,28,39,26]⟩
def cycle463_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data463 : PartitionData E W := ⟨6,![cycle463_0,cycle463_1,cycle463_2,cycle463_3,cycle463_4,cycle463_5]⟩
lemma valid_data463 : data463.Valid src463 dst463 Finset.univ := by decide +kernel

def src464 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst464 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle464_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle464_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle464_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle464_3 : CycleData E W := ⟨2,![9,17,22,12],![14,16,38,28]⟩
def cycle464_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle464_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data464 : PartitionData E W := ⟨6,![cycle464_0,cycle464_1,cycle464_2,cycle464_3,cycle464_4,cycle464_5]⟩
lemma valid_data464 : data464.Valid src464 dst464 Finset.univ := by decide +kernel

def src465 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,38,26,16,39,8,28,38,18,39]
def dst465 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,38,26,16,39,6,28,38,18,39,8]
def cycle465_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle465_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle465_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle465_3 : CycleData E W := ⟨3,![21,12,9,19,25],![8,28,14,16,39]⟩
def cycle465_4 : CycleData E W := ⟨2,![13,22,17,14],![5,28,38,26]⟩
def cycle465_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data465 : PartitionData E W := ⟨6,![cycle465_0,cycle465_1,cycle465_2,cycle465_3,cycle465_4,cycle465_5]⟩
lemma valid_data465 : data465.Valid src465 dst465 Finset.univ := by decide +kernel

def src466 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,38,26,16,39,8,28,39,18,38]
def dst466 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,38,26,16,39,6,28,39,18,38,8]
def cycle466_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle466_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle466_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle466_3 : CycleData E W := ⟨2,![9,19,22,12],![14,16,39,28]⟩
def cycle466_4 : CycleData E W := ⟨3,![13,21,25,17,14],![5,28,8,38,26]⟩
def cycle466_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data466 : PartitionData E W := ⟨6,![cycle466_0,cycle466_1,cycle466_2,cycle466_3,cycle466_4,cycle466_5]⟩
lemma valid_data466 : data466.Valid src466 dst466 Finset.univ := by decide +kernel

def src467 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst467 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle467_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle467_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,18]⟩
def cycle467_2 : CycleData E W := ⟨3,![5,4,15,18,10],![2,8,4,26,16]⟩
def cycle467_3 : CycleData E W := ⟨2,![9,19,24,12],![14,16,39,28]⟩
def cycle467_4 : CycleData E W := ⟨3,![13,23,22,17,14],![5,28,18,38,26]⟩
def cycle467_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data467 : PartitionData E W := ⟨6,![cycle467_0,cycle467_1,cycle467_2,cycle467_3,cycle467_4,cycle467_5]⟩
lemma valid_data467 : data467.Valid src467 dst467 Finset.univ := by decide +kernel

def src468 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,26,38,16,39,8,38,18,28,39]
def dst468 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle468_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle468_1 : CycleData E W := ⟨3,![3,11,17,22,7],![3,4,26,38,18]⟩
def cycle468_2 : CycleData E W := ⟨2,![4,25,24,15],![4,8,39,28]⟩
def cycle468_3 : CycleData E W := ⟨2,![5,21,18,10],![2,8,38,16]⟩
def cycle468_4 : CycleData E W := ⟨2,![13,8,23,14],![5,14,18,28]⟩
def cycle468_5 : CycleData E W := ⟨3,![16,12,9,19,20],![6,26,14,16,39]⟩
def data468 : PartitionData E W := ⟨6,![cycle468_0,cycle468_1,cycle468_2,cycle468_3,cycle468_4,cycle468_5]⟩
lemma valid_data468 : data468.Valid src468 dst468 Finset.univ := by decide +kernel

def src469 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,26,38,16,39,8,38,28,18,39]
def dst469 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle469_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle469_1 : CycleData E W := ⟨2,![3,15,23,7],![3,4,28,18]⟩
def cycle469_2 : CycleData E W := ⟨2,![4,21,17,11],![4,8,38,26]⟩
def cycle469_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle469_4 : CycleData E W := ⟨3,![16,12,8,24,20],![6,26,14,18,39]⟩
def cycle469_5 : CycleData E W := ⟨3,![13,9,18,22,14],![5,14,16,38,28]⟩
def data469 : PartitionData E W := ⟨6,![cycle469_0,cycle469_1,cycle469_2,cycle469_3,cycle469_4,cycle469_5]⟩
lemma valid_data469 : data469.Valid src469 dst469 Finset.univ := by decide +kernel

def src470 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,26,39,16,38,8,38,18,28,39]
def dst470 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle470_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle470_1 : CycleData E W := ⟨4,![3,11,16,20,22,7],![3,4,26,6,38,18]⟩
def cycle470_2 : CycleData E W := ⟨2,![4,25,24,15],![4,8,39,28]⟩
def cycle470_3 : CycleData E W := ⟨2,![5,21,19,10],![2,8,38,16]⟩
def cycle470_4 : CycleData E W := ⟨2,![13,8,23,14],![5,14,18,28]⟩
def cycle470_5 : CycleData E W := ⟨2,![9,18,17,12],![14,16,39,26]⟩
def data470 : PartitionData E W := ⟨6,![cycle470_0,cycle470_1,cycle470_2,cycle470_3,cycle470_4,cycle470_5]⟩
lemma valid_data470 : data470.Valid src470 dst470 Finset.univ := by decide +kernel

def src471 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,26,39,16,38,8,38,28,18,39]
def dst471 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle471_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle471_1 : CycleData E W := ⟨2,![3,15,23,7],![3,4,28,18]⟩
def cycle471_2 : CycleData E W := ⟨3,![4,21,20,16,11],![4,8,38,6,26]⟩
def cycle471_3 : CycleData E W := ⟨2,![5,25,18,10],![2,8,39,16]⟩
def cycle471_4 : CycleData E W := ⟨2,![8,24,17,12],![14,18,39,26]⟩
def cycle471_5 : CycleData E W := ⟨3,![13,9,19,22,14],![5,14,16,38,28]⟩
def data471 : PartitionData E W := ⟨6,![cycle471_0,cycle471_1,cycle471_2,cycle471_3,cycle471_4,cycle471_5]⟩
lemma valid_data471 : data471.Valid src471 dst471 Finset.univ := by decide +kernel

def src472 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,38,16,26,39,8,28,38,18,39]
def dst472 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle472_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle472_1 : CycleData E W := ⟨3,![3,11,12,8,7],![3,4,26,14,18]⟩
def cycle472_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle472_3 : CycleData E W := ⟨3,![5,25,19,18,10],![2,8,39,26,16]⟩
def cycle472_4 : CycleData E W := ⟨3,![13,9,17,22,14],![5,14,16,38,28]⟩
def cycle472_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data472 : PartitionData E W := ⟨6,![cycle472_0,cycle472_1,cycle472_2,cycle472_3,cycle472_4,cycle472_5]⟩
lemma valid_data472 : data472.Valid src472 dst472 Finset.univ := by decide +kernel

def src473 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,38,16,26,39,8,28,39,18,38]
def dst473 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle473_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle473_1 : CycleData E W := ⟨3,![3,11,12,8,7],![3,4,26,14,18]⟩
def cycle473_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle473_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle473_4 : CycleData E W := ⟨4,![13,9,18,19,22,14],![5,14,16,26,39,28]⟩
def cycle473_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data473 : PartitionData E W := ⟨6,![cycle473_0,cycle473_1,cycle473_2,cycle473_3,cycle473_4,cycle473_5]⟩
lemma valid_data473 : data473.Valid src473 dst473 Finset.univ := by decide +kernel

def src474 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst474 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle474_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle474_1 : CycleData E W := ⟨4,![3,15,14,13,8,7],![3,4,28,5,14,18]⟩
def cycle474_2 : CycleData E W := ⟨2,![4,25,19,11],![4,8,39,26]⟩
def cycle474_3 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle474_4 : CycleData E W := ⟨1,![9,18,12],![14,16,26]⟩
def cycle474_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,28,18,39]⟩
def data474 : PartitionData E W := ⟨6,![cycle474_0,cycle474_1,cycle474_2,cycle474_3,cycle474_4,cycle474_5]⟩
lemma valid_data474 : data474.Valid src474 dst474 Finset.univ := by decide +kernel

def src475 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,38,26,16,39,8,28,38,18,39]
def dst475 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle475_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle475_1 : CycleData E W := ⟨3,![3,11,12,8,7],![3,4,26,14,18]⟩
def cycle475_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle475_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle475_4 : CycleData E W := ⟨4,![13,9,18,17,22,14],![5,14,16,26,38,28]⟩
def cycle475_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data475 : PartitionData E W := ⟨6,![cycle475_0,cycle475_1,cycle475_2,cycle475_3,cycle475_4,cycle475_5]⟩
lemma valid_data475 : data475.Valid src475 dst475 Finset.univ := by decide +kernel

def src476 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,38,26,16,39,8,28,39,18,38]
def dst476 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle476_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle476_1 : CycleData E W := ⟨3,![3,11,12,8,7],![3,4,26,14,18]⟩
def cycle476_2 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle476_3 : CycleData E W := ⟨3,![5,25,17,18,10],![2,8,38,26,16]⟩
def cycle476_4 : CycleData E W := ⟨3,![13,9,19,22,14],![5,14,16,39,28]⟩
def cycle476_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data476 : PartitionData E W := ⟨6,![cycle476_0,cycle476_1,cycle476_2,cycle476_3,cycle476_4,cycle476_5]⟩
lemma valid_data476 : data476.Valid src476 dst476 Finset.univ := by decide +kernel

def src477 : E → W := ![2,5,6,3,4,8,2,3,18,14,16,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst477 : E → W := ![5,6,3,4,8,2,3,18,14,16,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle477_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,6,3]⟩
def cycle477_1 : CycleData E W := ⟨4,![3,15,14,13,8,7],![3,4,28,5,14,18]⟩
def cycle477_2 : CycleData E W := ⟨2,![4,21,17,11],![4,8,38,26]⟩
def cycle477_3 : CycleData E W := ⟨2,![5,25,19,10],![2,8,39,16]⟩
def cycle477_4 : CycleData E W := ⟨1,![9,18,12],![14,16,26]⟩
def cycle477_5 : CycleData E W := ⟨3,![16,22,23,24,20],![6,38,18,28,39]⟩
def data477 : PartitionData E W := ⟨6,![cycle477_0,cycle477_1,cycle477_2,cycle477_3,cycle477_4,cycle477_5]⟩
lemma valid_data477 : data477.Valid src477 dst477 Finset.univ := by decide +kernel

def src478 : E → W := ![2,5,6,3,4,8,2,14,3,16,18,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst478 : E → W := ![5,6,3,4,8,2,14,3,16,18,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle478_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle478_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,6,5,28,14]⟩
def cycle478_2 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle478_3 : CycleData E W := ⟨3,![6,14,19,24,10],![2,14,26,39,18]⟩
def cycle478_4 : CycleData E W := ⟨2,![9,23,22,17],![16,18,28,38]⟩
def cycle478_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data478 : PartitionData E W := ⟨6,![cycle478_0,cycle478_1,cycle478_2,cycle478_3,cycle478_4,cycle478_5]⟩
lemma valid_data478 : data478.Valid src478 dst478 Finset.univ := by decide +kernel

def src479 : E → W := ![2,5,6,3,4,8,2,14,3,16,18,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst479 : E → W := ![5,6,3,4,8,2,14,3,16,18,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle479_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle479_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,6,5,28,14]⟩
def cycle479_2 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle479_3 : CycleData E W := ⟨3,![6,14,17,22,10],![2,14,26,38,18]⟩
def cycle479_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle479_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data479 : PartitionData E W := ⟨6,![cycle479_0,cycle479_1,cycle479_2,cycle479_3,cycle479_4,cycle479_5]⟩
lemma valid_data479 : data479.Valid src479 dst479 Finset.univ := by decide +kernel

def src480 : E → W := ![2,5,6,3,4,8,2,14,3,18,16,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst480 : E → W := ![5,6,3,4,8,2,14,3,18,16,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle480_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle480_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,6,5,28,14]⟩
def cycle480_2 : CycleData E W := ⟨3,![3,15,19,24,8],![3,4,26,39,18]⟩
def cycle480_3 : CycleData E W := ⟨2,![6,14,18,10],![2,14,26,16]⟩
def cycle480_4 : CycleData E W := ⟨2,![9,23,22,17],![16,18,28,38]⟩
def cycle480_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data480 : PartitionData E W := ⟨6,![cycle480_0,cycle480_1,cycle480_2,cycle480_3,cycle480_4,cycle480_5]⟩
lemma valid_data480 : data480.Valid src480 dst480 Finset.univ := by decide +kernel

def src481 : E → W := ![2,5,6,3,4,8,2,14,3,18,16,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst481 : E → W := ![5,6,3,4,8,2,14,3,18,16,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle481_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle481_1 : CycleData E W := ⟨3,![2,1,12,13,7],![3,6,5,28,14]⟩
def cycle481_2 : CycleData E W := ⟨3,![3,15,17,22,8],![3,4,26,38,18]⟩
def cycle481_3 : CycleData E W := ⟨2,![6,14,18,10],![2,14,26,16]⟩
def cycle481_4 : CycleData E W := ⟨2,![9,23,24,19],![16,18,28,39]⟩
def cycle481_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data481 : PartitionData E W := ⟨6,![cycle481_0,cycle481_1,cycle481_2,cycle481_3,cycle481_4,cycle481_5]⟩
lemma valid_data481 : data481.Valid src481 dst481 Finset.univ := by decide +kernel

def src482 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,38,26,39,8,38,18,28,39]
def dst482 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle482_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle482_1 : CycleData E W := ⟨2,![1,20,24,12],![5,6,39,28]⟩
def cycle482_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle482_3 : CycleData E W := ⟨3,![3,15,14,7,8],![3,4,26,14,18]⟩
def cycle482_4 : CycleData E W := ⟨4,![6,13,23,22,17,10],![2,14,28,18,38,16]⟩
def cycle482_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data482 : PartitionData E W := ⟨6,![cycle482_0,cycle482_1,cycle482_2,cycle482_3,cycle482_4,cycle482_5]⟩
lemma valid_data482 : data482.Valid src482 dst482 Finset.univ := by decide +kernel

def src483 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,38,26,39,8,38,28,18,39]
def dst483 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle483_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle483_1 : CycleData E W := ⟨3,![1,16,17,22,12],![5,6,16,38,28]⟩
def cycle483_2 : CycleData E W := ⟨2,![2,20,24,8],![3,6,39,18]⟩
def cycle483_3 : CycleData E W := ⟨4,![6,14,15,3,9,10],![2,14,26,4,3,16]⟩
def cycle483_4 : CycleData E W := ⟨1,![7,23,13],![14,18,28]⟩
def cycle483_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data483 : PartitionData E W := ⟨6,![cycle483_0,cycle483_1,cycle483_2,cycle483_3,cycle483_4,cycle483_5]⟩
lemma valid_data483 : data483.Valid src483 dst483 Finset.univ := by decide +kernel

def src484 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,39,26,38,8,38,18,28,39]
def dst484 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle484_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle484_1 : CycleData E W := ⟨3,![1,20,22,23,12],![5,6,38,18,28]⟩
def cycle484_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle484_3 : CycleData E W := ⟨3,![3,15,14,7,8],![3,4,26,14,18]⟩
def cycle484_4 : CycleData E W := ⟨3,![6,13,24,17,10],![2,14,28,39,16]⟩
def cycle484_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data484 : PartitionData E W := ⟨6,![cycle484_0,cycle484_1,cycle484_2,cycle484_3,cycle484_4,cycle484_5]⟩
lemma valid_data484 : data484.Valid src484 dst484 Finset.univ := by decide +kernel

def src485 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,39,26,38,8,38,28,18,39]
def dst485 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle485_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle485_1 : CycleData E W := ⟨2,![1,20,22,12],![5,6,38,28]⟩
def cycle485_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle485_3 : CycleData E W := ⟨3,![3,15,14,7,8],![3,4,26,14,18]⟩
def cycle485_4 : CycleData E W := ⟨4,![6,13,23,24,17,10],![2,14,28,18,39,16]⟩
def cycle485_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data485 : PartitionData E W := ⟨6,![cycle485_0,cycle485_1,cycle485_2,cycle485_3,cycle485_4,cycle485_5]⟩
lemma valid_data485 : data485.Valid src485 dst485 Finset.univ := by decide +kernel

def src486 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,38,16,26,39,8,18,38,28,39]
def dst486 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle486_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle486_1 : CycleData E W := ⟨2,![1,16,23,12],![5,6,38,28]⟩
def cycle486_2 : CycleData E W := ⟨3,![2,20,19,15,3],![3,6,39,26,4]⟩
def cycle486_3 : CycleData E W := ⟨2,![6,14,18,10],![2,14,26,16]⟩
def cycle486_4 : CycleData E W := ⟨3,![21,7,13,24,25],![8,18,14,28,39]⟩
def cycle486_5 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def data486 : PartitionData E W := ⟨6,![cycle486_0,cycle486_1,cycle486_2,cycle486_3,cycle486_4,cycle486_5]⟩
lemma valid_data486 : data486.Valid src486 dst486 Finset.univ := by decide +kernel

def src487 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,38,16,26,39,8,18,39,28,38]
def dst487 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle487_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle487_1 : CycleData E W := ⟨2,![1,20,23,12],![5,6,39,28]⟩
def cycle487_2 : CycleData E W := ⟨2,![2,16,17,9],![3,6,38,16]⟩
def cycle487_3 : CycleData E W := ⟨3,![3,15,19,22,8],![3,4,26,39,18]⟩
def cycle487_4 : CycleData E W := ⟨2,![6,14,18,10],![2,14,26,16]⟩
def cycle487_5 : CycleData E W := ⟨3,![21,7,13,24,25],![8,18,14,28,38]⟩
def data487 : PartitionData E W := ⟨6,![cycle487_0,cycle487_1,cycle487_2,cycle487_3,cycle487_4,cycle487_5]⟩
lemma valid_data487 : data487.Valid src487 dst487 Finset.univ := by decide +kernel

def src488 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,38,16,26,39,8,38,28,18,39]
def dst488 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle488_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle488_1 : CycleData E W := ⟨2,![1,16,22,12],![5,6,38,28]⟩
def cycle488_2 : CycleData E W := ⟨3,![2,20,19,15,3],![3,6,39,26,4]⟩
def cycle488_3 : CycleData E W := ⟨2,![6,14,18,10],![2,14,26,16]⟩
def cycle488_4 : CycleData E W := ⟨1,![7,23,13],![14,18,28]⟩
def cycle488_5 : CycleData E W := ⟨4,![8,24,25,21,17,9],![3,18,39,8,38,16]⟩
def data488 : PartitionData E W := ⟨6,![cycle488_0,cycle488_1,cycle488_2,cycle488_3,cycle488_4,cycle488_5]⟩
lemma valid_data488 : data488.Valid src488 dst488 Finset.univ := by decide +kernel

def src489 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,38,26,16,39,8,18,38,28,39]
def dst489 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle489_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle489_1 : CycleData E W := ⟨2,![1,16,23,12],![5,6,38,28]⟩
def cycle489_2 : CycleData E W := ⟨2,![2,20,19,9],![3,6,39,16]⟩
def cycle489_3 : CycleData E W := ⟨3,![3,15,17,22,8],![3,4,26,38,18]⟩
def cycle489_4 : CycleData E W := ⟨2,![6,14,18,10],![2,14,26,16]⟩
def cycle489_5 : CycleData E W := ⟨3,![21,7,13,24,25],![8,18,14,28,39]⟩
def data489 : PartitionData E W := ⟨6,![cycle489_0,cycle489_1,cycle489_2,cycle489_3,cycle489_4,cycle489_5]⟩
lemma valid_data489 : data489.Valid src489 dst489 Finset.univ := by decide +kernel

def src490 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,38,26,16,39,8,18,39,28,38]
def dst490 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle490_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle490_1 : CycleData E W := ⟨2,![1,20,23,12],![5,6,39,28]⟩
def cycle490_2 : CycleData E W := ⟨3,![2,16,17,15,3],![3,6,38,26,4]⟩
def cycle490_3 : CycleData E W := ⟨2,![6,14,18,10],![2,14,26,16]⟩
def cycle490_4 : CycleData E W := ⟨3,![21,7,13,24,25],![8,18,14,28,38]⟩
def cycle490_5 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def data490 : PartitionData E W := ⟨6,![cycle490_0,cycle490_1,cycle490_2,cycle490_3,cycle490_4,cycle490_5]⟩
lemma valid_data490 : data490.Valid src490 dst490 Finset.univ := by decide +kernel

def src491 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,5,28,14,26,6,38,26,16,39,8,38,18,28,39]
def dst491 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,5,28,14,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle491_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,8]⟩
def cycle491_1 : CycleData E W := ⟨3,![2,1,12,23,8],![3,6,5,28,18]⟩
def cycle491_2 : CycleData E W := ⟨2,![3,15,18,9],![3,4,26,16]⟩
def cycle491_3 : CycleData E W := ⟨3,![6,13,24,19,10],![2,14,28,39,16]⟩
def cycle491_4 : CycleData E W := ⟨2,![7,22,17,14],![14,18,38,26]⟩
def cycle491_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data491 : PartitionData E W := ⟨6,![cycle491_0,cycle491_1,cycle491_2,cycle491_3,cycle491_4,cycle491_5]⟩
lemma valid_data491 : data491.Valid src491 dst491 Finset.univ := by decide +kernel

def src492 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,26,38,39,8,38,18,28,39]
def dst492 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,26,38,39,6,38,18,28,39,8]
def cycle492_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle492_1 : CycleData E W := ⟨2,![1,20,24,14],![5,6,39,28]⟩
def cycle492_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle492_3 : CycleData E W := ⟨2,![3,15,23,8],![3,4,28,18]⟩
def cycle492_4 : CycleData E W := ⟨3,![5,4,11,17,10],![2,8,4,26,16]⟩
def cycle492_5 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def cycle492_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data492 : PartitionData E W := ⟨7,![cycle492_0,cycle492_1,cycle492_2,cycle492_3,cycle492_4,cycle492_5,cycle492_6]⟩
lemma valid_data492 : data492.Valid src492 dst492 Finset.univ := by decide +kernel

def src493 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,26,39,38,8,38,28,18,39]
def dst493 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,26,39,38,6,38,28,18,39,8]
def cycle493_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle493_1 : CycleData E W := ⟨2,![1,20,22,14],![5,6,38,28]⟩
def cycle493_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle493_3 : CycleData E W := ⟨2,![3,15,23,8],![3,4,28,18]⟩
def cycle493_4 : CycleData E W := ⟨3,![5,4,11,17,10],![2,8,4,26,16]⟩
def cycle493_5 : CycleData E W := ⟨2,![7,24,18,12],![14,18,39,26]⟩
def cycle493_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data493 : PartitionData E W := ⟨7,![cycle493_0,cycle493_1,cycle493_2,cycle493_3,cycle493_4,cycle493_5,cycle493_6]⟩
lemma valid_data493 : data493.Valid src493 dst493 Finset.univ := by decide +kernel

def src494 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,39,8,28,38,18,39]
def dst494 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,39,6,28,38,18,39,8]
def cycle494_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle494_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle494_2 : CycleData E W := ⟨3,![4,21,22,18,11],![4,8,28,38,26]⟩
def cycle494_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle494_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle494_5 : CycleData E W := ⟨2,![8,23,17,9],![3,18,38,16]⟩
def data494 : PartitionData E W := ⟨6,![cycle494_0,cycle494_1,cycle494_2,cycle494_3,cycle494_4,cycle494_5]⟩
lemma valid_data494 : data494.Valid src494 dst494 Finset.univ := by decide +kernel

def src495 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,39,8,28,39,18,38]
def dst495 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,39,6,28,39,18,38,8]
def cycle495_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle495_1 : CycleData E W := ⟨2,![1,20,22,14],![5,6,39,28]⟩
def cycle495_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle495_3 : CycleData E W := ⟨3,![3,11,12,7,8],![3,4,26,14,18]⟩
def cycle495_4 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle495_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,38,16]⟩
def cycle495_6 : CycleData E W := ⟨2,![23,19,18,24],![18,39,26,38]⟩
def data495 : PartitionData E W := ⟨7,![cycle495_0,cycle495_1,cycle495_2,cycle495_3,cycle495_4,cycle495_5,cycle495_6]⟩
lemma valid_data495 : data495.Valid src495 dst495 Finset.univ := by decide +kernel

def src496 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,39,8,38,18,28,39]
def dst496 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle496_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle496_1 : CycleData E W := ⟨2,![1,20,24,14],![5,6,39,28]⟩
def cycle496_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle496_3 : CycleData E W := ⟨2,![3,15,23,8],![3,4,28,18]⟩
def cycle496_4 : CycleData E W := ⟨2,![4,25,19,11],![4,8,39,26]⟩
def cycle496_5 : CycleData E W := ⟨2,![5,21,17,10],![2,8,38,16]⟩
def cycle496_6 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def data496 : PartitionData E W := ⟨7,![cycle496_0,cycle496_1,cycle496_2,cycle496_3,cycle496_4,cycle496_5,cycle496_6]⟩
lemma valid_data496 : data496.Valid src496 dst496 Finset.univ := by decide +kernel

def src497 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,39,8,38,28,18,39]
def dst497 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle497_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle497_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle497_2 : CycleData E W := ⟨2,![4,21,18,11],![4,8,38,26]⟩
def cycle497_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle497_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle497_5 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def data497 : PartitionData E W := ⟨6,![cycle497_0,cycle497_1,cycle497_2,cycle497_3,cycle497_4,cycle497_5]⟩
lemma valid_data497 : data497.Valid src497 dst497 Finset.univ := by decide +kernel

def src498 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,39,26,8,38,28,18,39]
def dst498 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,39,26,6,38,28,18,39,8]
def cycle498_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle498_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,6,5,28,4]⟩
def cycle498_2 : CycleData E W := ⟨4,![5,4,11,20,16,10],![2,8,4,26,6,16]⟩
def cycle498_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle498_4 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def cycle498_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data498 : PartitionData E W := ⟨6,![cycle498_0,cycle498_1,cycle498_2,cycle498_3,cycle498_4,cycle498_5]⟩
lemma valid_data498 : data498.Valid src498 dst498 Finset.univ := by decide +kernel

def src499 : E → W := ![2,5,6,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,39,26,38,8,28,38,18,39]
def dst499 : E → W := ![5,6,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,39,26,38,6,28,38,18,39,8]
def cycle499_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle499_1 : CycleData E W := ⟨2,![1,20,22,14],![5,6,38,28]⟩
def cycle499_2 : CycleData E W := ⟨1,![2,16,9],![3,6,16]⟩
def cycle499_3 : CycleData E W := ⟨3,![3,11,12,7,8],![3,4,26,14,18]⟩
def cycle499_4 : CycleData E W := ⟨1,![4,21,15],![4,8,28]⟩
def cycle499_5 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle499_6 : CycleData E W := ⟨2,![23,19,18,24],![18,38,26,39]⟩
def data499 : PartitionData E W := ⟨7,![cycle499_0,cycle499_1,cycle499_2,cycle499_3,cycle499_4,cycle499_5,cycle499_6]⟩
lemma valid_data499 : data499.Valid src499 dst499 Finset.univ := by decide +kernel

def lookupB9 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data450 else (if j < 2 then data451 else data452)) else (if j < 4 then data453 else (if j < 5 then data454 else data455))) else (if j < 9 then (if j < 7 then data456 else (if j < 8 then data457 else data458)) else (if j < 10 then data459 else (if j < 11 then data460 else data461)))) else (if j < 18 then (if j < 15 then (if j < 13 then data462 else (if j < 14 then data463 else data464)) else (if j < 16 then data465 else (if j < 17 then data466 else data467))) else (if j < 21 then (if j < 19 then data468 else (if j < 20 then data469 else data470)) else (if j < 23 then (if j < 22 then data471 else data472) else (if j < 24 then data473 else data474))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data475 else (if j < 27 then data476 else data477)) else (if j < 29 then data478 else (if j < 30 then data479 else data480))) else (if j < 34 then (if j < 32 then data481 else (if j < 33 then data482 else data483)) else (if j < 35 then data484 else (if j < 36 then data485 else data486)))) else (if j < 43 then (if j < 40 then (if j < 38 then data487 else (if j < 39 then data488 else data489)) else (if j < 41 then data490 else (if j < 42 then data491 else data492))) else (if j < 46 then (if j < 44 then data493 else (if j < 45 then data494 else data495)) else (if j < 48 then (if j < 47 then data496 else data497) else (if j < 49 then data498 else data499))))))

def srcTableB9 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src450 else (if j < 2 then src451 else src452)) else (if j < 4 then src453 else (if j < 5 then src454 else src455))) else (if j < 9 then (if j < 7 then src456 else (if j < 8 then src457 else src458)) else (if j < 10 then src459 else (if j < 11 then src460 else src461)))) else (if j < 18 then (if j < 15 then (if j < 13 then src462 else (if j < 14 then src463 else src464)) else (if j < 16 then src465 else (if j < 17 then src466 else src467))) else (if j < 21 then (if j < 19 then src468 else (if j < 20 then src469 else src470)) else (if j < 23 then (if j < 22 then src471 else src472) else (if j < 24 then src473 else src474))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src475 else (if j < 27 then src476 else src477)) else (if j < 29 then src478 else (if j < 30 then src479 else src480))) else (if j < 34 then (if j < 32 then src481 else (if j < 33 then src482 else src483)) else (if j < 35 then src484 else (if j < 36 then src485 else src486)))) else (if j < 43 then (if j < 40 then (if j < 38 then src487 else (if j < 39 then src488 else src489)) else (if j < 41 then src490 else (if j < 42 then src491 else src492))) else (if j < 46 then (if j < 44 then src493 else (if j < 45 then src494 else src495)) else (if j < 48 then (if j < 47 then src496 else src497) else (if j < 49 then src498 else src499))))))

def dstTableB9 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst450 else (if j < 2 then dst451 else dst452)) else (if j < 4 then dst453 else (if j < 5 then dst454 else dst455))) else (if j < 9 then (if j < 7 then dst456 else (if j < 8 then dst457 else dst458)) else (if j < 10 then dst459 else (if j < 11 then dst460 else dst461)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst462 else (if j < 14 then dst463 else dst464)) else (if j < 16 then dst465 else (if j < 17 then dst466 else dst467))) else (if j < 21 then (if j < 19 then dst468 else (if j < 20 then dst469 else dst470)) else (if j < 23 then (if j < 22 then dst471 else dst472) else (if j < 24 then dst473 else dst474))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst475 else (if j < 27 then dst476 else dst477)) else (if j < 29 then dst478 else (if j < 30 then dst479 else dst480))) else (if j < 34 then (if j < 32 then dst481 else (if j < 33 then dst482 else dst483)) else (if j < 35 then dst484 else (if j < 36 then dst485 else dst486)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst487 else (if j < 39 then dst488 else dst489)) else (if j < 41 then dst490 else (if j < 42 then dst491 else dst492))) else (if j < 46 then (if j < 44 then dst493 else (if j < 45 then dst494 else dst495)) else (if j < 48 then (if j < 47 then dst496 else dst497) else (if j < 49 then dst498 else dst499))))))

def caseB9 (i : Fin 50) : Cases := ⟨450 + i.val,by have := i.isLt; omega⟩
lemma tableB9_valid (i : Fin 50) :
    (lookupB9 i.val).Valid (srcTableB9 i.val) (dstTableB9 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB9_row : ∀ (i : Fin 50) (e : E),
    srcTableB9 i.val e = caseSource (caseB9 i) e := by decide +kernel

lemma dstB9_row : ∀ (i : Fin 50) (e : E),
    dstTableB9 i.val e = caseTarget (caseB9 i) e := by decide +kernel

lemma sizeB9 : ∀ i : Fin 50, (lookupB9 i.val).size ≤ 5 →
    (lookupB9 i.val).size = 2 ∧
      (⟨caseKey (caseB9 i),caseKey_lt (caseB9 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB9 (i : Fin 50) : Certificate (caseB9 i) := by
  refine ⟨lookupB9 i.val,?_,sizeB9 i⟩
  have hv := tableB9_valid i
  rw [funext (srcB9_row i),funext (dstB9_row i)] at hv
  exact hv
lemma certificateInterval9 : FiniteIntervals.Covers CertificateAt 450 500 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 450 50 (fun i _ => certificateB9 i)
#print axioms certificateInterval9
end Erdos184Work.FiveRows4

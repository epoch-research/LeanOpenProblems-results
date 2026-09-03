import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src550 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,39,26,38,8,38,28,18,39]
def dst550 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle550_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle550_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle550_2 : CycleData E W := ⟨2,![4,21,19,15],![4,8,38,26]⟩
def cycle550_3 : CycleData E W := ⟨2,![5,25,17,6],![2,8,39,16]⟩
def cycle550_4 : CycleData E W := ⟨3,![16,7,12,22,20],![6,16,14,28,38]⟩
def cycle550_5 : CycleData E W := ⟨3,![13,23,24,18,14],![5,28,18,39,26]⟩
def data550 : PartitionData E W := ⟨6,![cycle550_0,cycle550_1,cycle550_2,cycle550_3,cycle550_4,cycle550_5]⟩
lemma valid_data550 : data550.Valid src550 dst550 Finset.univ := by decide +kernel

def src551 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,16,39,38,26,8,38,18,28,39]
def dst551 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,16,39,38,26,6,38,18,28,39,8]
def cycle551_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle551_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle551_2 : CycleData E W := ⟨4,![5,4,15,20,16,6],![2,8,4,26,6,16]⟩
def cycle551_3 : CycleData E W := ⟨2,![7,17,24,12],![14,16,39,28]⟩
def cycle551_4 : CycleData E W := ⟨3,![13,23,22,19,14],![5,28,18,38,26]⟩
def cycle551_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data551 : PartitionData E W := ⟨6,![cycle551_0,cycle551_1,cycle551_2,cycle551_3,cycle551_4,cycle551_5]⟩
lemma valid_data551 : data551.Valid src551 dst551 Finset.univ := by decide +kernel

def src552 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,16,38,39,8,38,28,18,39]
def dst552 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,16,38,39,6,38,28,18,39,8]
def cycle552_0 : CycleData E W := ⟨2,![0,13,23,10],![2,5,28,18]⟩
def cycle552_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle552_2 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle552_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle552_4 : CycleData E W := ⟨3,![5,4,15,17,6],![2,8,4,26,16]⟩
def cycle552_5 : CycleData E W := ⟨2,![7,18,22,12],![14,16,38,28]⟩
def cycle552_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data552 : PartitionData E W := ⟨7,![cycle552_0,cycle552_1,cycle552_2,cycle552_3,cycle552_4,cycle552_5,cycle552_6]⟩
lemma valid_data552 : data552.Valid src552 dst552 Finset.univ := by decide +kernel

def src553 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,16,39,38,8,38,18,28,39]
def dst553 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,16,39,38,6,38,18,28,39,8]
def cycle553_0 : CycleData E W := ⟨2,![0,13,23,10],![2,5,28,18]⟩
def cycle553_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle553_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle553_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle553_4 : CycleData E W := ⟨3,![5,4,15,17,6],![2,8,4,26,16]⟩
def cycle553_5 : CycleData E W := ⟨2,![7,18,24,12],![14,16,39,28]⟩
def cycle553_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data553 : PartitionData E W := ⟨7,![cycle553_0,cycle553_1,cycle553_2,cycle553_3,cycle553_4,cycle553_5,cycle553_6]⟩
lemma valid_data553 : data553.Valid src553 dst553 Finset.univ := by decide +kernel

def src554 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,38,16,39,8,18,38,28,39]
def dst554 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,38,16,39,6,18,38,28,39,8]
def cycle554_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle554_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle554_2 : CycleData E W := ⟨3,![4,21,22,17,15],![4,8,18,38,26]⟩
def cycle554_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle554_4 : CycleData E W := ⟨2,![7,18,23,12],![14,16,38,28]⟩
def cycle554_5 : CycleData E W := ⟨3,![13,24,20,16,14],![5,28,39,6,26]⟩
def data554 : PartitionData E W := ⟨6,![cycle554_0,cycle554_1,cycle554_2,cycle554_3,cycle554_4,cycle554_5]⟩
lemma valid_data554 : data554.Valid src554 dst554 Finset.univ := by decide +kernel

def src555 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,38,16,39,8,18,39,28,38]
def dst555 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,38,16,39,6,18,39,28,38,8]
def cycle555_0 : CycleData E W := ⟨3,![0,13,12,7,6],![2,5,28,14,16]⟩
def cycle555_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle555_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,39,18]⟩
def cycle555_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle555_4 : CycleData E W := ⟨2,![4,25,17,15],![4,8,38,26]⟩
def cycle555_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle555_6 : CycleData E W := ⟨2,![18,24,23,19],![16,38,28,39]⟩
def data555 : PartitionData E W := ⟨7,![cycle555_0,cycle555_1,cycle555_2,cycle555_3,cycle555_4,cycle555_5,cycle555_6]⟩
lemma valid_data555 : data555.Valid src555 dst555 Finset.univ := by decide +kernel

def src556 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,38,16,39,8,38,18,28,39]
def dst556 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,38,16,39,6,38,18,28,39,8]
def cycle556_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle556_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle556_2 : CycleData E W := ⟨2,![4,21,17,15],![4,8,38,26]⟩
def cycle556_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle556_4 : CycleData E W := ⟨3,![7,18,22,23,12],![14,16,38,18,28]⟩
def cycle556_5 : CycleData E W := ⟨3,![13,24,20,16,14],![5,28,39,6,26]⟩
def data556 : PartitionData E W := ⟨6,![cycle556_0,cycle556_1,cycle556_2,cycle556_3,cycle556_4,cycle556_5]⟩
lemma valid_data556 : data556.Valid src556 dst556 Finset.univ := by decide +kernel

def src557 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,38,16,39,8,38,28,18,39]
def dst557 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,38,16,39,6,38,28,18,39,8]
def cycle557_0 : CycleData E W := ⟨2,![0,13,23,10],![2,5,28,18]⟩
def cycle557_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle557_2 : CycleData E W := ⟨2,![2,20,24,9],![3,6,39,18]⟩
def cycle557_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle557_4 : CycleData E W := ⟨2,![4,21,17,15],![4,8,38,26]⟩
def cycle557_5 : CycleData E W := ⟨2,![5,25,19,6],![2,8,39,16]⟩
def cycle557_6 : CycleData E W := ⟨2,![7,18,22,12],![14,16,38,28]⟩
def data557 : PartitionData E W := ⟨7,![cycle557_0,cycle557_1,cycle557_2,cycle557_3,cycle557_4,cycle557_5,cycle557_6]⟩
lemma valid_data557 : data557.Valid src557 dst557 Finset.univ := by decide +kernel

def src558 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,39,16,38,8,18,38,28,39]
def dst558 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,39,16,38,6,18,38,28,39,8]
def cycle558_0 : CycleData E W := ⟨3,![0,13,12,7,6],![2,5,28,14,16]⟩
def cycle558_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle558_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle558_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle558_4 : CycleData E W := ⟨2,![4,25,17,15],![4,8,39,26]⟩
def cycle558_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle558_6 : CycleData E W := ⟨2,![18,24,23,19],![16,39,28,38]⟩
def data558 : PartitionData E W := ⟨7,![cycle558_0,cycle558_1,cycle558_2,cycle558_3,cycle558_4,cycle558_5,cycle558_6]⟩
lemma valid_data558 : data558.Valid src558 dst558 Finset.univ := by decide +kernel

def src559 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,39,16,38,8,18,39,28,38]
def dst559 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,39,16,38,6,18,39,28,38,8]
def cycle559_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle559_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle559_2 : CycleData E W := ⟨3,![4,21,22,17,15],![4,8,18,39,26]⟩
def cycle559_3 : CycleData E W := ⟨2,![5,25,19,6],![2,8,38,16]⟩
def cycle559_4 : CycleData E W := ⟨2,![7,18,23,12],![14,16,39,28]⟩
def cycle559_5 : CycleData E W := ⟨3,![13,24,20,16,14],![5,28,38,6,26]⟩
def data559 : PartitionData E W := ⟨6,![cycle559_0,cycle559_1,cycle559_2,cycle559_3,cycle559_4,cycle559_5]⟩
lemma valid_data559 : data559.Valid src559 dst559 Finset.univ := by decide +kernel

def src560 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,39,16,38,8,38,18,28,39]
def dst560 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,39,16,38,6,38,18,28,39,8]
def cycle560_0 : CycleData E W := ⟨2,![0,13,23,10],![2,5,28,18]⟩
def cycle560_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle560_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,38,18]⟩
def cycle560_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle560_4 : CycleData E W := ⟨2,![4,25,17,15],![4,8,39,26]⟩
def cycle560_5 : CycleData E W := ⟨2,![5,21,19,6],![2,8,38,16]⟩
def cycle560_6 : CycleData E W := ⟨2,![7,18,24,12],![14,16,39,28]⟩
def data560 : PartitionData E W := ⟨7,![cycle560_0,cycle560_1,cycle560_2,cycle560_3,cycle560_4,cycle560_5,cycle560_6]⟩
lemma valid_data560 : data560.Valid src560 dst560 Finset.univ := by decide +kernel

def src561 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,26,39,16,38,8,38,28,18,39]
def dst561 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,26,39,16,38,6,38,28,18,39,8]
def cycle561_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle561_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle561_2 : CycleData E W := ⟨3,![4,21,20,16,15],![4,8,38,6,26]⟩
def cycle561_3 : CycleData E W := ⟨2,![5,25,18,6],![2,8,39,16]⟩
def cycle561_4 : CycleData E W := ⟨2,![7,19,22,12],![14,16,38,28]⟩
def cycle561_5 : CycleData E W := ⟨3,![13,23,24,17,14],![5,28,18,39,26]⟩
def data561 : PartitionData E W := ⟨6,![cycle561_0,cycle561_1,cycle561_2,cycle561_3,cycle561_4,cycle561_5]⟩
lemma valid_data561 : data561.Valid src561 dst561 Finset.univ := by decide +kernel

def src562 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,18,28,38,39]
def dst562 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,18,28,38,39,8]
def cycle562_0 : CycleData E W := ⟨2,![0,14,18,6],![2,5,26,16]⟩
def cycle562_1 : CycleData E W := ⟨3,![2,1,13,22,9],![3,6,5,28,18]⟩
def cycle562_2 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle562_3 : CycleData E W := ⟨2,![4,25,19,15],![4,8,39,26]⟩
def cycle562_4 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle562_5 : CycleData E W := ⟨2,![7,17,23,12],![14,16,38,28]⟩
def cycle562_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data562 : PartitionData E W := ⟨7,![cycle562_0,cycle562_1,cycle562_2,cycle562_3,cycle562_4,cycle562_5,cycle562_6]⟩
lemma valid_data562 : data562.Valid src562 dst562 Finset.univ := by decide +kernel

def src563 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,18,38,28,39]
def dst563 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle563_0 : CycleData E W := ⟨2,![0,14,18,6],![2,5,26,16]⟩
def cycle563_1 : CycleData E W := ⟨2,![1,20,24,13],![5,6,39,28]⟩
def cycle563_2 : CycleData E W := ⟨2,![2,16,22,9],![3,6,38,18]⟩
def cycle563_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle563_4 : CycleData E W := ⟨2,![4,25,19,15],![4,8,39,26]⟩
def cycle563_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle563_6 : CycleData E W := ⟨2,![7,17,23,12],![14,16,38,28]⟩
def data563 : PartitionData E W := ⟨7,![cycle563_0,cycle563_1,cycle563_2,cycle563_3,cycle563_4,cycle563_5,cycle563_6]⟩
lemma valid_data563 : data563.Valid src563 dst563 Finset.univ := by decide +kernel

def src564 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,18,39,28,38]
def dst564 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle564_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle564_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle564_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle564_3 : CycleData E W := ⟨2,![7,17,24,12],![14,16,38,28]⟩
def cycle564_4 : CycleData E W := ⟨2,![13,23,19,14],![5,28,39,26]⟩
def cycle564_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data564 : PartitionData E W := ⟨6,![cycle564_0,cycle564_1,cycle564_2,cycle564_3,cycle564_4,cycle564_5]⟩
lemma valid_data564 : data564.Valid src564 dst564 Finset.univ := by decide +kernel

def src565 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,18,39,38,28]
def dst565 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,18,39,38,28,8]
def cycle565_0 : CycleData E W := ⟨4,![0,1,2,8,7,6],![2,5,6,3,14,16]⟩
def cycle565_1 : CycleData E W := ⟨3,![3,15,19,22,9],![3,4,26,39,18]⟩
def cycle565_2 : CycleData E W := ⟨2,![4,25,12,11],![4,8,28,14]⟩
def cycle565_3 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle565_4 : CycleData E W := ⟨3,![13,24,17,18,14],![5,28,38,16,26]⟩
def cycle565_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data565 : PartitionData E W := ⟨6,![cycle565_0,cycle565_1,cycle565_2,cycle565_3,cycle565_4,cycle565_5]⟩
lemma valid_data565 : data565.Valid src565 dst565 Finset.univ := by decide +kernel

def src566 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,28,18,39,38]
def dst566 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,28,18,39,38,8]
def cycle566_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle566_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle566_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle566_3 : CycleData E W := ⟨3,![21,12,7,17,25],![8,28,14,16,38]⟩
def cycle566_4 : CycleData E W := ⟨3,![13,22,23,19,14],![5,28,18,39,26]⟩
def cycle566_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data566 : PartitionData E W := ⟨6,![cycle566_0,cycle566_1,cycle566_2,cycle566_3,cycle566_4,cycle566_5]⟩
lemma valid_data566 : data566.Valid src566 dst566 Finset.univ := by decide +kernel

def src567 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,28,38,18,39]
def dst567 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,28,38,18,39,8]
def cycle567_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle567_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle567_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle567_3 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle567_4 : CycleData E W := ⟨3,![13,21,25,19,14],![5,28,8,39,26]⟩
def cycle567_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data567 : PartitionData E W := ⟨6,![cycle567_0,cycle567_1,cycle567_2,cycle567_3,cycle567_4,cycle567_5]⟩
lemma valid_data567 : data567.Valid src567 dst567 Finset.univ := by decide +kernel

def src568 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,28,39,18,38]
def dst568 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,28,39,18,38,8]
def cycle568_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle568_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle568_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle568_3 : CycleData E W := ⟨3,![21,12,7,17,25],![8,28,14,16,38]⟩
def cycle568_4 : CycleData E W := ⟨2,![13,22,19,14],![5,28,39,26]⟩
def cycle568_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data568 : PartitionData E W := ⟨6,![cycle568_0,cycle568_1,cycle568_2,cycle568_3,cycle568_4,cycle568_5]⟩
lemma valid_data568 : data568.Valid src568 dst568 Finset.univ := by decide +kernel

def src569 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst569 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle569_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle569_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle569_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle569_3 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle569_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle569_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data569 : PartitionData E W := ⟨6,![cycle569_0,cycle569_1,cycle569_2,cycle569_3,cycle569_4,cycle569_5]⟩
lemma valid_data569 : data569.Valid src569 dst569 Finset.univ := by decide +kernel

def src570 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,18,28,39,38]
def dst570 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,18,28,39,38,8]
def cycle570_0 : CycleData E W := ⟨2,![0,14,18,6],![2,5,26,16]⟩
def cycle570_1 : CycleData E W := ⟨3,![2,1,13,22,9],![3,6,5,28,18]⟩
def cycle570_2 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle570_3 : CycleData E W := ⟨2,![4,25,17,15],![4,8,38,26]⟩
def cycle570_4 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle570_5 : CycleData E W := ⟨2,![7,19,23,12],![14,16,39,28]⟩
def cycle570_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data570 : PartitionData E W := ⟨7,![cycle570_0,cycle570_1,cycle570_2,cycle570_3,cycle570_4,cycle570_5,cycle570_6]⟩
lemma valid_data570 : data570.Valid src570 dst570 Finset.univ := by decide +kernel

def src571 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,18,38,28,39]
def dst571 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle571_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle571_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle571_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle571_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle571_4 : CycleData E W := ⟨2,![13,23,17,14],![5,28,38,26]⟩
def cycle571_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data571 : PartitionData E W := ⟨6,![cycle571_0,cycle571_1,cycle571_2,cycle571_3,cycle571_4,cycle571_5]⟩
lemma valid_data571 : data571.Valid src571 dst571 Finset.univ := by decide +kernel

def src572 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,18,38,39,28]
def dst572 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,18,38,39,28,8]
def cycle572_0 : CycleData E W := ⟨4,![0,1,2,8,7,6],![2,5,6,3,14,16]⟩
def cycle572_1 : CycleData E W := ⟨3,![3,15,17,22,9],![3,4,26,38,18]⟩
def cycle572_2 : CycleData E W := ⟨2,![4,25,12,11],![4,8,28,14]⟩
def cycle572_3 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle572_4 : CycleData E W := ⟨3,![13,24,19,18,14],![5,28,39,16,26]⟩
def cycle572_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data572 : PartitionData E W := ⟨6,![cycle572_0,cycle572_1,cycle572_2,cycle572_3,cycle572_4,cycle572_5]⟩
lemma valid_data572 : data572.Valid src572 dst572 Finset.univ := by decide +kernel

def src573 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,18,39,28,38]
def dst573 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle573_0 : CycleData E W := ⟨2,![0,14,18,6],![2,5,26,16]⟩
def cycle573_1 : CycleData E W := ⟨2,![1,16,24,13],![5,6,38,28]⟩
def cycle573_2 : CycleData E W := ⟨2,![2,20,22,9],![3,6,39,18]⟩
def cycle573_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle573_4 : CycleData E W := ⟨2,![4,25,17,15],![4,8,38,26]⟩
def cycle573_5 : CycleData E W := ⟨1,![5,21,10],![2,8,18]⟩
def cycle573_6 : CycleData E W := ⟨2,![7,19,23,12],![14,16,39,28]⟩
def data573 : PartitionData E W := ⟨7,![cycle573_0,cycle573_1,cycle573_2,cycle573_3,cycle573_4,cycle573_5,cycle573_6]⟩
lemma valid_data573 : data573.Valid src573 dst573 Finset.univ := by decide +kernel

def src574 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,28,18,38,39]
def dst574 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,28,18,38,39,8]
def cycle574_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle574_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle574_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle574_3 : CycleData E W := ⟨3,![21,12,7,19,25],![8,28,14,16,39]⟩
def cycle574_4 : CycleData E W := ⟨3,![13,22,23,17,14],![5,28,18,38,26]⟩
def cycle574_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data574 : PartitionData E W := ⟨6,![cycle574_0,cycle574_1,cycle574_2,cycle574_3,cycle574_4,cycle574_5]⟩
lemma valid_data574 : data574.Valid src574 dst574 Finset.univ := by decide +kernel

def src575 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,28,38,18,39]
def dst575 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,28,38,18,39,8]
def cycle575_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle575_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle575_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle575_3 : CycleData E W := ⟨3,![21,12,7,19,25],![8,28,14,16,39]⟩
def cycle575_4 : CycleData E W := ⟨2,![13,22,17,14],![5,28,38,26]⟩
def cycle575_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,18,39]⟩
def data575 : PartitionData E W := ⟨6,![cycle575_0,cycle575_1,cycle575_2,cycle575_3,cycle575_4,cycle575_5]⟩
lemma valid_data575 : data575.Valid src575 dst575 Finset.univ := by decide +kernel

def src576 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,28,39,18,38]
def dst576 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,28,39,18,38,8]
def cycle576_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle576_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle576_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle576_3 : CycleData E W := ⟨2,![7,19,22,12],![14,16,39,28]⟩
def cycle576_4 : CycleData E W := ⟨3,![13,21,25,17,14],![5,28,8,38,26]⟩
def cycle576_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,18,39]⟩
def data576 : PartitionData E W := ⟨6,![cycle576_0,cycle576_1,cycle576_2,cycle576_3,cycle576_4,cycle576_5]⟩
lemma valid_data576 : data576.Valid src576 dst576 Finset.univ := by decide +kernel

def src577 : E → W := ![2,5,6,3,4,8,2,16,14,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst577 : E → W := ![5,6,3,4,8,2,16,14,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle577_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,5,6,3,18]⟩
def cycle577_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle577_2 : CycleData E W := ⟨3,![5,4,15,18,6],![2,8,4,26,16]⟩
def cycle577_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle577_4 : CycleData E W := ⟨3,![13,23,22,17,14],![5,28,18,38,26]⟩
def cycle577_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data577 : PartitionData E W := ⟨6,![cycle577_0,cycle577_1,cycle577_2,cycle577_3,cycle577_4,cycle577_5]⟩
lemma valid_data577 : data577.Valid src577 dst577 Finset.univ := by decide +kernel

def src578 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst578 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle578_0 : CycleData E W := ⟨2,![0,11,3,6],![2,5,4,3]⟩
def cycle578_1 : CycleData E W := ⟨2,![1,25,19,12],![5,8,39,26]⟩
def cycle578_2 : CycleData E W := ⟨2,![2,21,17,7],![3,8,38,16]⟩
def cycle578_3 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle578_4 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle578_5 : CycleData E W := ⟨1,![8,18,13],![14,16,26]⟩
def cycle578_6 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def data578 : PartitionData E W := ⟨7,![cycle578_0,cycle578_1,cycle578_2,cycle578_3,cycle578_4,cycle578_5,cycle578_6]⟩
lemma valid_data578 : data578.Valid src578 dst578 Finset.univ := by decide +kernel

def src579 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst579 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle579_0 : CycleData E W := ⟨2,![0,11,3,6],![2,5,4,3]⟩
def cycle579_1 : CycleData E W := ⟨2,![1,21,17,12],![5,8,38,26]⟩
def cycle579_2 : CycleData E W := ⟨2,![2,25,19,7],![3,8,39,16]⟩
def cycle579_3 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle579_4 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle579_5 : CycleData E W := ⟨1,![8,18,13],![14,16,26]⟩
def cycle579_6 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def data579 : PartitionData E W := ⟨7,![cycle579_0,cycle579_1,cycle579_2,cycle579_3,cycle579_4,cycle579_5,cycle579_6]⟩
lemma valid_data579 : data579.Valid src579 dst579 Finset.univ := by decide +kernel

def src580 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,5,26,28,6,38,16,26,39,8,38,28,18,39]
def dst580 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,5,26,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle580_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle580_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle580_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle580_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle580_4 : CycleData E W := ⟨3,![12,9,23,14,13],![5,14,18,28,26]⟩
def cycle580_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data580 : PartitionData E W := ⟨6,![cycle580_0,cycle580_1,cycle580_2,cycle580_3,cycle580_4,cycle580_5]⟩
lemma valid_data580 : data580.Valid src580 dst580 Finset.univ := by decide +kernel

def src581 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,5,26,28,6,38,26,16,39,8,38,18,28,39]
def dst581 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,5,26,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle581_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle581_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle581_2 : CycleData E W := ⟨3,![5,4,15,23,10],![2,6,4,28,18]⟩
def cycle581_3 : CycleData E W := ⟨3,![12,9,22,17,13],![5,14,18,38,26]⟩
def cycle581_4 : CycleData E W := ⟨2,![18,14,24,19],![16,26,28,39]⟩
def cycle581_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data581 : PartitionData E W := ⟨6,![cycle581_0,cycle581_1,cycle581_2,cycle581_3,cycle581_4,cycle581_5]⟩
lemma valid_data581 : data581.Valid src581 dst581 Finset.univ := by decide +kernel

def src582 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,5,28,26,6,38,16,26,39,8,38,28,18,39]
def dst582 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,5,28,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle582_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle582_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle582_2 : CycleData E W := ⟨3,![4,16,17,18,15],![4,6,38,16,26]⟩
def cycle582_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle582_4 : CycleData E W := ⟨2,![12,9,23,13],![5,14,18,28]⟩
def cycle582_5 : CycleData E W := ⟨3,![21,22,14,19,25],![8,38,28,26,39]⟩
def data582 : PartitionData E W := ⟨6,![cycle582_0,cycle582_1,cycle582_2,cycle582_3,cycle582_4,cycle582_5]⟩
lemma valid_data582 : data582.Valid src582 dst582 Finset.univ := by decide +kernel

def src583 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,5,28,26,6,38,26,16,39,8,38,18,28,39]
def dst583 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,5,28,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle583_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle583_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle583_2 : CycleData E W := ⟨2,![4,16,17,15],![4,6,38,26]⟩
def cycle583_3 : CycleData E W := ⟨4,![5,20,25,21,22,10],![2,6,39,8,38,18]⟩
def cycle583_4 : CycleData E W := ⟨2,![12,9,23,13],![5,14,18,28]⟩
def cycle583_5 : CycleData E W := ⟨2,![18,14,24,19],![16,26,28,39]⟩
def data583 : PartitionData E W := ⟨6,![cycle583_0,cycle583_1,cycle583_2,cycle583_3,cycle583_4,cycle583_5]⟩
lemma valid_data583 : data583.Valid src583 dst583 Finset.univ := by decide +kernel

def src584 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,26,38,16,39,8,38,18,28,39]
def dst584 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle584_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle584_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle584_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle584_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle584_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle584_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data584 : PartitionData E W := ⟨6,![cycle584_0,cycle584_1,cycle584_2,cycle584_3,cycle584_4,cycle584_5]⟩
lemma valid_data584 : data584.Valid src584 dst584 Finset.univ := by decide +kernel

def src585 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,26,38,16,39,8,38,28,18,39]
def dst585 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle585_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle585_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle585_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle585_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle585_4 : CycleData E W := ⟨3,![9,23,22,17,12],![14,18,28,38,26]⟩
def cycle585_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data585 : PartitionData E W := ⟨6,![cycle585_0,cycle585_1,cycle585_2,cycle585_3,cycle585_4,cycle585_5]⟩
lemma valid_data585 : data585.Valid src585 dst585 Finset.univ := by decide +kernel

def src586 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,26,39,16,38,8,38,18,28,39]
def dst586 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle586_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle586_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle586_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle586_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle586_4 : CycleData E W := ⟨3,![9,23,24,17,12],![14,18,28,39,26]⟩
def cycle586_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data586 : PartitionData E W := ⟨6,![cycle586_0,cycle586_1,cycle586_2,cycle586_3,cycle586_4,cycle586_5]⟩
lemma valid_data586 : data586.Valid src586 dst586 Finset.univ := by decide +kernel

def src587 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,26,39,16,38,8,38,28,18,39]
def dst587 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle587_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle587_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle587_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle587_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle587_4 : CycleData E W := ⟨2,![9,24,17,12],![14,18,39,26]⟩
def cycle587_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data587 : PartitionData E W := ⟨6,![cycle587_0,cycle587_1,cycle587_2,cycle587_3,cycle587_4,cycle587_5]⟩
lemma valid_data587 : data587.Valid src587 dst587 Finset.univ := by decide +kernel

def src588 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,38,16,26,39,8,28,38,18,39]
def dst588 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle588_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle588_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle588_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle588_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle588_4 : CycleData E W := ⟨3,![9,23,17,18,12],![14,18,38,16,26]⟩
def cycle588_5 : CycleData E W := ⟨3,![13,19,25,21,14],![5,26,39,8,28]⟩
def data588 : PartitionData E W := ⟨6,![cycle588_0,cycle588_1,cycle588_2,cycle588_3,cycle588_4,cycle588_5]⟩
lemma valid_data588 : data588.Valid src588 dst588 Finset.univ := by decide +kernel

def src589 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,38,16,26,39,8,28,39,18,38]
def dst589 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle589_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle589_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle589_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle589_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle589_4 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def cycle589_5 : CycleData E W := ⟨4,![13,18,17,25,21,14],![5,26,16,38,8,28]⟩
def data589 : PartitionData E W := ⟨6,![cycle589_0,cycle589_1,cycle589_2,cycle589_3,cycle589_4,cycle589_5]⟩
lemma valid_data589 : data589.Valid src589 dst589 Finset.univ := by decide +kernel

def src590 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst590 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle590_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle590_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle590_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle590_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle590_4 : CycleData E W := ⟨3,![13,12,9,23,14],![5,26,14,18,28]⟩
def cycle590_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data590 : PartitionData E W := ⟨6,![cycle590_0,cycle590_1,cycle590_2,cycle590_3,cycle590_4,cycle590_5]⟩
lemma valid_data590 : data590.Valid src590 dst590 Finset.univ := by decide +kernel

def src591 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,38,26,16,39,8,28,38,18,39]
def dst591 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle591_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle591_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle591_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle591_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle591_4 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def cycle591_5 : CycleData E W := ⟨4,![13,18,19,25,21,14],![5,26,16,39,8,28]⟩
def data591 : PartitionData E W := ⟨6,![cycle591_0,cycle591_1,cycle591_2,cycle591_3,cycle591_4,cycle591_5]⟩
lemma valid_data591 : data591.Valid src591 dst591 Finset.univ := by decide +kernel

def src592 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,38,26,16,39,8,28,39,18,38]
def dst592 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle592_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle592_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle592_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle592_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle592_4 : CycleData E W := ⟨3,![9,23,19,18,12],![14,18,39,16,26]⟩
def cycle592_5 : CycleData E W := ⟨3,![13,17,25,21,14],![5,26,38,8,28]⟩
def data592 : PartitionData E W := ⟨6,![cycle592_0,cycle592_1,cycle592_2,cycle592_3,cycle592_4,cycle592_5]⟩
lemma valid_data592 : data592.Valid src592 dst592 Finset.univ := by decide +kernel

def src593 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst593 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle593_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle593_1 : CycleData E W := ⟨2,![3,11,8,7],![3,4,14,16]⟩
def cycle593_2 : CycleData E W := ⟨3,![5,4,15,23,10],![2,6,4,28,18]⟩
def cycle593_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle593_4 : CycleData E W := ⟨3,![13,18,19,24,14],![5,26,16,39,28]⟩
def cycle593_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data593 : PartitionData E W := ⟨6,![cycle593_0,cycle593_1,cycle593_2,cycle593_3,cycle593_4,cycle593_5]⟩
lemma valid_data593 : data593.Valid src593 dst593 Finset.univ := by decide +kernel

def src594 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,26,38,16,39,8,38,18,28,39]
def dst594 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle594_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle594_1 : CycleData E W := ⟨4,![3,11,12,13,8,7],![3,4,26,5,14,16]⟩
def cycle594_2 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle594_3 : CycleData E W := ⟨3,![5,16,17,22,10],![2,6,26,38,18]⟩
def cycle594_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle594_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data594 : PartitionData E W := ⟨6,![cycle594_0,cycle594_1,cycle594_2,cycle594_3,cycle594_4,cycle594_5]⟩
lemma valid_data594 : data594.Valid src594 dst594 Finset.univ := by decide +kernel

def src595 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,26,38,16,39,8,38,28,18,39]
def dst595 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle595_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle595_1 : CycleData E W := ⟨4,![3,11,12,13,8,7],![3,4,26,5,14,16]⟩
def cycle595_2 : CycleData E W := ⟨3,![4,16,17,22,15],![4,6,26,38,28]⟩
def cycle595_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle595_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle595_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data595 : PartitionData E W := ⟨6,![cycle595_0,cycle595_1,cycle595_2,cycle595_3,cycle595_4,cycle595_5]⟩
lemma valid_data595 : data595.Valid src595 dst595 Finset.univ := by decide +kernel

def src596 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,26,39,16,38,8,38,18,28,39]
def dst596 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle596_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle596_1 : CycleData E W := ⟨4,![3,11,12,13,8,7],![3,4,26,5,14,16]⟩
def cycle596_2 : CycleData E W := ⟨3,![4,16,17,24,15],![4,6,26,39,28]⟩
def cycle596_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle596_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle596_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data596 : PartitionData E W := ⟨6,![cycle596_0,cycle596_1,cycle596_2,cycle596_3,cycle596_4,cycle596_5]⟩
lemma valid_data596 : data596.Valid src596 dst596 Finset.univ := by decide +kernel

def src597 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,26,39,16,38,8,38,28,18,39]
def dst597 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle597_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle597_1 : CycleData E W := ⟨4,![3,11,12,13,8,7],![3,4,26,5,14,16]⟩
def cycle597_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,38,28]⟩
def cycle597_3 : CycleData E W := ⟨3,![5,16,17,24,10],![2,6,26,39,18]⟩
def cycle597_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle597_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data597 : PartitionData E W := ⟨6,![cycle597_0,cycle597_1,cycle597_2,cycle597_3,cycle597_4,cycle597_5]⟩
lemma valid_data597 : data597.Valid src597 dst597 Finset.univ := by decide +kernel

def src598 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,38,16,26,39,8,28,38,18,39]
def dst598 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle598_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle598_1 : CycleData E W := ⟨3,![3,4,16,17,7],![3,4,6,38,16]⟩
def cycle598_2 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle598_3 : CycleData E W := ⟨2,![12,18,8,13],![5,26,16,14]⟩
def cycle598_4 : CycleData E W := ⟨2,![9,23,22,14],![14,18,38,28]⟩
def cycle598_5 : CycleData E W := ⟨3,![11,19,25,21,15],![4,26,39,8,28]⟩
def data598 : PartitionData E W := ⟨6,![cycle598_0,cycle598_1,cycle598_2,cycle598_3,cycle598_4,cycle598_5]⟩
lemma valid_data598 : data598.Valid src598 dst598 Finset.univ := by decide +kernel

def src599 : E → W := ![2,5,8,3,4,6,2,3,16,14,18,4,26,5,14,28,6,38,16,26,39,8,28,39,18,38]
def dst599 : E → W := ![5,8,3,4,6,2,3,16,14,18,2,26,5,14,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle599_0 : CycleData E W := ⟨2,![0,1,2,6],![2,5,8,3]⟩
def cycle599_1 : CycleData E W := ⟨3,![3,4,16,17,7],![3,4,6,38,16]⟩
def cycle599_2 : CycleData E W := ⟨2,![5,20,23,10],![2,6,39,18]⟩
def cycle599_3 : CycleData E W := ⟨2,![12,18,8,13],![5,26,16,14]⟩
def cycle599_4 : CycleData E W := ⟨3,![21,14,9,24,25],![8,28,14,18,38]⟩
def cycle599_5 : CycleData E W := ⟨2,![11,19,22,15],![4,26,39,28]⟩
def data599 : PartitionData E W := ⟨6,![cycle599_0,cycle599_1,cycle599_2,cycle599_3,cycle599_4,cycle599_5]⟩
lemma valid_data599 : data599.Valid src599 dst599 Finset.univ := by decide +kernel

def lookupB11 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data550 else (if j < 2 then data551 else data552)) else (if j < 4 then data553 else (if j < 5 then data554 else data555))) else (if j < 9 then (if j < 7 then data556 else (if j < 8 then data557 else data558)) else (if j < 10 then data559 else (if j < 11 then data560 else data561)))) else (if j < 18 then (if j < 15 then (if j < 13 then data562 else (if j < 14 then data563 else data564)) else (if j < 16 then data565 else (if j < 17 then data566 else data567))) else (if j < 21 then (if j < 19 then data568 else (if j < 20 then data569 else data570)) else (if j < 23 then (if j < 22 then data571 else data572) else (if j < 24 then data573 else data574))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data575 else (if j < 27 then data576 else data577)) else (if j < 29 then data578 else (if j < 30 then data579 else data580))) else (if j < 34 then (if j < 32 then data581 else (if j < 33 then data582 else data583)) else (if j < 35 then data584 else (if j < 36 then data585 else data586)))) else (if j < 43 then (if j < 40 then (if j < 38 then data587 else (if j < 39 then data588 else data589)) else (if j < 41 then data590 else (if j < 42 then data591 else data592))) else (if j < 46 then (if j < 44 then data593 else (if j < 45 then data594 else data595)) else (if j < 48 then (if j < 47 then data596 else data597) else (if j < 49 then data598 else data599))))))

def srcTableB11 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src550 else (if j < 2 then src551 else src552)) else (if j < 4 then src553 else (if j < 5 then src554 else src555))) else (if j < 9 then (if j < 7 then src556 else (if j < 8 then src557 else src558)) else (if j < 10 then src559 else (if j < 11 then src560 else src561)))) else (if j < 18 then (if j < 15 then (if j < 13 then src562 else (if j < 14 then src563 else src564)) else (if j < 16 then src565 else (if j < 17 then src566 else src567))) else (if j < 21 then (if j < 19 then src568 else (if j < 20 then src569 else src570)) else (if j < 23 then (if j < 22 then src571 else src572) else (if j < 24 then src573 else src574))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src575 else (if j < 27 then src576 else src577)) else (if j < 29 then src578 else (if j < 30 then src579 else src580))) else (if j < 34 then (if j < 32 then src581 else (if j < 33 then src582 else src583)) else (if j < 35 then src584 else (if j < 36 then src585 else src586)))) else (if j < 43 then (if j < 40 then (if j < 38 then src587 else (if j < 39 then src588 else src589)) else (if j < 41 then src590 else (if j < 42 then src591 else src592))) else (if j < 46 then (if j < 44 then src593 else (if j < 45 then src594 else src595)) else (if j < 48 then (if j < 47 then src596 else src597) else (if j < 49 then src598 else src599))))))

def dstTableB11 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst550 else (if j < 2 then dst551 else dst552)) else (if j < 4 then dst553 else (if j < 5 then dst554 else dst555))) else (if j < 9 then (if j < 7 then dst556 else (if j < 8 then dst557 else dst558)) else (if j < 10 then dst559 else (if j < 11 then dst560 else dst561)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst562 else (if j < 14 then dst563 else dst564)) else (if j < 16 then dst565 else (if j < 17 then dst566 else dst567))) else (if j < 21 then (if j < 19 then dst568 else (if j < 20 then dst569 else dst570)) else (if j < 23 then (if j < 22 then dst571 else dst572) else (if j < 24 then dst573 else dst574))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst575 else (if j < 27 then dst576 else dst577)) else (if j < 29 then dst578 else (if j < 30 then dst579 else dst580))) else (if j < 34 then (if j < 32 then dst581 else (if j < 33 then dst582 else dst583)) else (if j < 35 then dst584 else (if j < 36 then dst585 else dst586)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst587 else (if j < 39 then dst588 else dst589)) else (if j < 41 then dst590 else (if j < 42 then dst591 else dst592))) else (if j < 46 then (if j < 44 then dst593 else (if j < 45 then dst594 else dst595)) else (if j < 48 then (if j < 47 then dst596 else dst597) else (if j < 49 then dst598 else dst599))))))

def caseB11 (i : Fin 50) : Cases := ⟨550 + i.val,by have := i.isLt; omega⟩
lemma tableB11_valid (i : Fin 50) :
    (lookupB11 i.val).Valid (srcTableB11 i.val) (dstTableB11 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB11_row : ∀ (i : Fin 50) (e : E),
    srcTableB11 i.val e = caseSource (caseB11 i) e := by decide +kernel

lemma dstB11_row : ∀ (i : Fin 50) (e : E),
    dstTableB11 i.val e = caseTarget (caseB11 i) e := by decide +kernel

lemma sizeB11 : ∀ i : Fin 50, (lookupB11 i.val).size ≤ 5 →
    (lookupB11 i.val).size = 2 ∧
      (⟨caseKey (caseB11 i),caseKey_lt (caseB11 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB11 (i : Fin 50) : Certificate (caseB11 i) := by
  refine ⟨lookupB11 i.val,?_,sizeB11 i⟩
  have hv := tableB11_valid i
  rw [funext (srcB11_row i),funext (dstB11_row i)] at hv
  exact hv
lemma certificateInterval11 : FiniteIntervals.Covers CertificateAt 550 600 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 550 50 (fun i _ => certificateB11 i)
#print axioms certificateInterval11
end Erdos184Work.FiveRows4

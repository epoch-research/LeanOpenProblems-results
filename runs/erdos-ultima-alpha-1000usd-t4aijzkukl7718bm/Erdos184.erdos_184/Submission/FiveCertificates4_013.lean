import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src650 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,18,38,39,28]
def dst650 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,18,38,39,28,8]
def cycle650_0 : CycleData E W := ⟨3,![0,12,11,4,5],![2,5,26,4,6]⟩
def cycle650_1 : CycleData E W := ⟨3,![6,13,1,21,10],![2,14,5,8,18]⟩
def cycle650_2 : CycleData E W := ⟨2,![2,25,15,3],![3,8,28,4]⟩
def cycle650_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle650_4 : CycleData E W := ⟨3,![8,18,17,22,9],![3,16,26,38,18]⟩
def cycle650_5 : CycleData E W := ⟨1,![16,23,20],![6,38,39]⟩
def data650 : PartitionData E W := ⟨6,![cycle650_0,cycle650_1,cycle650_2,cycle650_3,cycle650_4,cycle650_5]⟩
lemma valid_data650 : data650.Valid src650 dst650 Finset.univ := by decide +kernel

def src651 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,18,39,28,38]
def dst651 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle651_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle651_1 : CycleData E W := ⟨2,![1,25,17,12],![5,8,38,26]⟩
def cycle651_2 : CycleData E W := ⟨1,![2,21,9],![3,8,18]⟩
def cycle651_3 : CycleData E W := ⟨2,![3,11,18,8],![3,4,26,16]⟩
def cycle651_4 : CycleData E W := ⟨2,![4,16,24,15],![4,6,38,28]⟩
def cycle651_5 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle651_6 : CycleData E W := ⟨2,![7,19,23,14],![14,16,39,28]⟩
def data651 : PartitionData E W := ⟨7,![cycle651_0,cycle651_1,cycle651_2,cycle651_3,cycle651_4,cycle651_5,cycle651_6]⟩
lemma valid_data651 : data651.Valid src651 dst651 Finset.univ := by decide +kernel

def src652 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,28,18,38,39]
def dst652 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,28,18,38,39,8]
def cycle652_0 : CycleData E W := ⟨3,![0,12,11,4,5],![2,5,26,4,6]⟩
def cycle652_1 : CycleData E W := ⟨2,![1,21,14,13],![5,8,28,14]⟩
def cycle652_2 : CycleData E W := ⟨2,![2,25,19,8],![3,8,39,16]⟩
def cycle652_3 : CycleData E W := ⟨2,![3,15,22,9],![3,4,28,18]⟩
def cycle652_4 : CycleData E W := ⟨4,![6,7,18,17,23,10],![2,14,16,26,38,18]⟩
def cycle652_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data652 : PartitionData E W := ⟨6,![cycle652_0,cycle652_1,cycle652_2,cycle652_3,cycle652_4,cycle652_5]⟩
lemma valid_data652 : data652.Valid src652 dst652 Finset.univ := by decide +kernel

def src653 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,28,38,18,39]
def dst653 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle653_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle653_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle653_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle653_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle653_4 : CycleData E W := ⟨3,![21,14,7,19,25],![8,28,14,16,39]⟩
def cycle653_5 : CycleData E W := ⟨3,![8,18,17,23,9],![3,16,26,38,18]⟩
def data653 : PartitionData E W := ⟨6,![cycle653_0,cycle653_1,cycle653_2,cycle653_3,cycle653_4,cycle653_5]⟩
lemma valid_data653 : data653.Valid src653 dst653 Finset.univ := by decide +kernel

def src654 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,28,39,18,38]
def dst654 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle654_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle654_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle654_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle654_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle654_4 : CycleData E W := ⟨4,![21,14,7,18,17,25],![8,28,14,16,26,38]⟩
def cycle654_5 : CycleData E W := ⟨2,![8,19,23,9],![3,16,39,18]⟩
def data654 : PartitionData E W := ⟨6,![cycle654_0,cycle654_1,cycle654_2,cycle654_3,cycle654_4,cycle654_5]⟩
lemma valid_data654 : data654.Valid src654 dst654 Finset.univ := by decide +kernel

def src655 : E → W := ![2,5,8,3,4,6,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst655 : E → W := ![5,8,3,4,6,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle655_0 : CycleData E W := ⟨1,![0,13,6],![2,5,14]⟩
def cycle655_1 : CycleData E W := ⟨3,![2,1,12,11,3],![3,8,5,26,4]⟩
def cycle655_2 : CycleData E W := ⟨3,![5,4,15,23,10],![2,6,4,28,18]⟩
def cycle655_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle655_4 : CycleData E W := ⟨3,![8,18,17,22,9],![3,16,26,38,18]⟩
def cycle655_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data655 : PartitionData E W := ⟨6,![cycle655_0,cycle655_1,cycle655_2,cycle655_3,cycle655_4,cycle655_5]⟩
lemma valid_data655 : data655.Valid src655 dst655 Finset.univ := by decide +kernel

def src656 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,16,38,26,39,8,38,18,28,39]
def dst656 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle656_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle656_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,26,14]⟩
def cycle656_2 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle656_3 : CycleData E W := ⟨3,![5,16,17,22,10],![2,6,16,38,18]⟩
def cycle656_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle656_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data656 : PartitionData E W := ⟨6,![cycle656_0,cycle656_1,cycle656_2,cycle656_3,cycle656_4,cycle656_5]⟩
lemma valid_data656 : data656.Valid src656 dst656 Finset.univ := by decide +kernel

def src657 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,16,38,26,39,8,38,28,18,39]
def dst657 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle657_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle657_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,26,14]⟩
def cycle657_2 : CycleData E W := ⟨3,![4,16,17,22,15],![4,6,16,38,28]⟩
def cycle657_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle657_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle657_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data657 : PartitionData E W := ⟨6,![cycle657_0,cycle657_1,cycle657_2,cycle657_3,cycle657_4,cycle657_5]⟩
lemma valid_data657 : data657.Valid src657 dst657 Finset.univ := by decide +kernel

def src658 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,16,39,26,38,8,38,18,28,39]
def dst658 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle658_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle658_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,26,14]⟩
def cycle658_2 : CycleData E W := ⟨3,![4,16,17,24,15],![4,6,16,39,28]⟩
def cycle658_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle658_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle658_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data658 : PartitionData E W := ⟨6,![cycle658_0,cycle658_1,cycle658_2,cycle658_3,cycle658_4,cycle658_5]⟩
lemma valid_data658 : data658.Valid src658 dst658 Finset.univ := by decide +kernel

def src659 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,16,39,26,38,8,38,28,18,39]
def dst659 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle659_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle659_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,26,14]⟩
def cycle659_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,38,28]⟩
def cycle659_3 : CycleData E W := ⟨3,![5,16,17,24,10],![2,6,16,39,18]⟩
def cycle659_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle659_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,26,39]⟩
def data659 : PartitionData E W := ⟨6,![cycle659_0,cycle659_1,cycle659_2,cycle659_3,cycle659_4,cycle659_5]⟩
lemma valid_data659 : data659.Valid src659 dst659 Finset.univ := by decide +kernel

def src660 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,38,16,26,39,8,18,38,28,39]
def dst660 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle660_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle660_1 : CycleData E W := ⟨3,![2,1,12,18,7],![3,8,5,26,16]⟩
def cycle660_2 : CycleData E W := ⟨2,![3,15,14,8],![3,4,28,14]⟩
def cycle660_3 : CycleData E W := ⟨2,![6,17,22,10],![2,16,38,18]⟩
def cycle660_4 : CycleData E W := ⟨3,![21,9,13,19,25],![8,18,14,26,39]⟩
def cycle660_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data660 : PartitionData E W := ⟨6,![cycle660_0,cycle660_1,cycle660_2,cycle660_3,cycle660_4,cycle660_5]⟩
lemma valid_data660 : data660.Valid src660 dst660 Finset.univ := by decide +kernel

def src661 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,38,16,26,39,8,18,39,28,38]
def dst661 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle661_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle661_1 : CycleData E W := ⟨3,![2,1,12,18,7],![3,8,5,26,16]⟩
def cycle661_2 : CycleData E W := ⟨2,![3,15,14,8],![3,4,28,14]⟩
def cycle661_3 : CycleData E W := ⟨3,![6,17,25,21,10],![2,16,38,8,18]⟩
def cycle661_4 : CycleData E W := ⟨2,![9,22,19,13],![14,18,39,26]⟩
def cycle661_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data661 : PartitionData E W := ⟨6,![cycle661_0,cycle661_1,cycle661_2,cycle661_3,cycle661_4,cycle661_5]⟩
lemma valid_data661 : data661.Valid src661 dst661 Finset.univ := by decide +kernel

def src662 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,38,16,26,39,8,38,28,18,39]
def dst662 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle662_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle662_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,26,14]⟩
def cycle662_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle662_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle662_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle662_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data662 : PartitionData E W := ⟨6,![cycle662_0,cycle662_1,cycle662_2,cycle662_3,cycle662_4,cycle662_5]⟩
lemma valid_data662 : data662.Valid src662 dst662 Finset.univ := by decide +kernel

def src663 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,38,26,16,39,8,18,38,28,39]
def dst663 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle663_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle663_1 : CycleData E W := ⟨3,![2,1,12,18,7],![3,8,5,26,16]⟩
def cycle663_2 : CycleData E W := ⟨2,![3,15,14,8],![3,4,28,14]⟩
def cycle663_3 : CycleData E W := ⟨3,![6,19,25,21,10],![2,16,39,8,18]⟩
def cycle663_4 : CycleData E W := ⟨2,![9,22,17,13],![14,18,38,26]⟩
def cycle663_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data663 : PartitionData E W := ⟨6,![cycle663_0,cycle663_1,cycle663_2,cycle663_3,cycle663_4,cycle663_5]⟩
lemma valid_data663 : data663.Valid src663 dst663 Finset.univ := by decide +kernel

def src664 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,38,26,16,39,8,18,39,28,38]
def dst664 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle664_0 : CycleData E W := ⟨2,![0,11,4,5],![2,5,4,6]⟩
def cycle664_1 : CycleData E W := ⟨3,![2,1,12,18,7],![3,8,5,26,16]⟩
def cycle664_2 : CycleData E W := ⟨2,![3,15,14,8],![3,4,28,14]⟩
def cycle664_3 : CycleData E W := ⟨2,![6,19,22,10],![2,16,39,18]⟩
def cycle664_4 : CycleData E W := ⟨3,![21,9,13,17,25],![8,18,14,26,38]⟩
def cycle664_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data664 : PartitionData E W := ⟨6,![cycle664_0,cycle664_1,cycle664_2,cycle664_3,cycle664_4,cycle664_5]⟩
lemma valid_data664 : data664.Valid src664 dst664 Finset.univ := by decide +kernel

def src665 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,5,26,14,28,6,38,26,16,39,8,38,18,28,39]
def dst665 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,5,26,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle665_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle665_1 : CycleData E W := ⟨3,![3,11,12,13,8],![3,4,5,26,14]⟩
def cycle665_2 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle665_3 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle665_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle665_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,26,16,39]⟩
def data665 : PartitionData E W := ⟨6,![cycle665_0,cycle665_1,cycle665_2,cycle665_3,cycle665_4,cycle665_5]⟩
lemma valid_data665 : data665.Valid src665 dst665 Finset.univ := by decide +kernel

def src666 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,26,38,39,8,38,18,28,39]
def dst666 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,26,38,39,6,38,18,28,39,8]
def cycle666_0 : CycleData E W := ⟨2,![0,14,23,10],![2,5,28,18]⟩
def cycle666_1 : CycleData E W := ⟨3,![2,1,13,17,7],![3,8,5,26,16]⟩
def cycle666_2 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle666_3 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle666_4 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle666_5 : CycleData E W := ⟨2,![9,22,18,12],![14,18,38,26]⟩
def cycle666_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data666 : PartitionData E W := ⟨7,![cycle666_0,cycle666_1,cycle666_2,cycle666_3,cycle666_4,cycle666_5,cycle666_6]⟩
lemma valid_data666 : data666.Valid src666 dst666 Finset.univ := by decide +kernel

def src667 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,26,39,38,8,38,28,18,39]
def dst667 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,26,39,38,6,38,28,18,39,8]
def cycle667_0 : CycleData E W := ⟨2,![0,14,23,10],![2,5,28,18]⟩
def cycle667_1 : CycleData E W := ⟨3,![2,1,13,17,7],![3,8,5,26,16]⟩
def cycle667_2 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle667_3 : CycleData E W := ⟨2,![4,20,22,15],![4,6,38,28]⟩
def cycle667_4 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle667_5 : CycleData E W := ⟨2,![9,24,18,12],![14,18,39,26]⟩
def cycle667_6 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data667 : PartitionData E W := ⟨7,![cycle667_0,cycle667_1,cycle667_2,cycle667_3,cycle667_4,cycle667_5,cycle667_6]⟩
lemma valid_data667 : data667.Valid src667 dst667 Finset.univ := by decide +kernel

def src668 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,38,26,39,8,28,38,18,39]
def dst668 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,38,26,39,6,28,38,18,39,8]
def cycle668_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle668_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle668_2 : CycleData E W := ⟨3,![4,16,17,22,15],![4,6,16,38,28]⟩
def cycle668_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle668_4 : CycleData E W := ⟨2,![9,23,18,12],![14,18,38,26]⟩
def cycle668_5 : CycleData E W := ⟨3,![13,19,25,21,14],![5,26,39,8,28]⟩
def data668 : PartitionData E W := ⟨6,![cycle668_0,cycle668_1,cycle668_2,cycle668_3,cycle668_4,cycle668_5]⟩
lemma valid_data668 : data668.Valid src668 dst668 Finset.univ := by decide +kernel

def src669 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,38,26,39,8,28,39,18,38]
def dst669 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,38,26,39,6,28,39,18,38,8]
def cycle669_0 : CycleData E W := ⟨3,![0,13,12,9,10],![2,5,26,14,18]⟩
def cycle669_1 : CycleData E W := ⟨1,![1,21,14],![5,8,28]⟩
def cycle669_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,38,16]⟩
def cycle669_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle669_4 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle669_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle669_6 : CycleData E W := ⟨2,![23,19,18,24],![18,39,26,38]⟩
def data669 : PartitionData E W := ⟨7,![cycle669_0,cycle669_1,cycle669_2,cycle669_3,cycle669_4,cycle669_5,cycle669_6]⟩
lemma valid_data669 : data669.Valid src669 dst669 Finset.univ := by decide +kernel

def src670 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,38,26,39,8,38,18,28,39]
def dst670 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle670_0 : CycleData E W := ⟨2,![0,14,23,10],![2,5,28,18]⟩
def cycle670_1 : CycleData E W := ⟨2,![1,25,19,13],![5,8,39,26]⟩
def cycle670_2 : CycleData E W := ⟨2,![2,21,17,7],![3,8,38,16]⟩
def cycle670_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle670_4 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle670_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle670_6 : CycleData E W := ⟨2,![9,22,18,12],![14,18,38,26]⟩
def data670 : PartitionData E W := ⟨7,![cycle670_0,cycle670_1,cycle670_2,cycle670_3,cycle670_4,cycle670_5,cycle670_6]⟩
lemma valid_data670 : data670.Valid src670 dst670 Finset.univ := by decide +kernel

def src671 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,38,26,39,8,38,28,18,39]
def dst671 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle671_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle671_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle671_2 : CycleData E W := ⟨3,![4,16,17,22,15],![4,6,16,38,28]⟩
def cycle671_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle671_4 : CycleData E W := ⟨3,![13,12,9,23,14],![5,26,14,18,28]⟩
def cycle671_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,26,39]⟩
def data671 : PartitionData E W := ⟨6,![cycle671_0,cycle671_1,cycle671_2,cycle671_3,cycle671_4,cycle671_5]⟩
lemma valid_data671 : data671.Valid src671 dst671 Finset.univ := by decide +kernel

def src672 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,38,39,26,8,38,28,18,39]
def dst672 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,38,39,26,6,38,28,18,39,8]
def cycle672_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle672_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle672_2 : CycleData E W := ⟨3,![4,20,13,14,15],![4,6,26,5,28]⟩
def cycle672_3 : CycleData E W := ⟨4,![5,16,17,22,23,10],![2,6,16,38,28,18]⟩
def cycle672_4 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle672_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data672 : PartitionData E W := ⟨6,![cycle672_0,cycle672_1,cycle672_2,cycle672_3,cycle672_4,cycle672_5]⟩
lemma valid_data672 : data672.Valid src672 dst672 Finset.univ := by decide +kernel

def src673 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,39,26,38,8,28,38,18,39]
def dst673 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,39,26,38,6,28,38,18,39,8]
def cycle673_0 : CycleData E W := ⟨3,![0,13,12,9,10],![2,5,26,14,18]⟩
def cycle673_1 : CycleData E W := ⟨1,![1,21,14],![5,8,28]⟩
def cycle673_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,39,16]⟩
def cycle673_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle673_4 : CycleData E W := ⟨2,![4,20,22,15],![4,6,38,28]⟩
def cycle673_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle673_6 : CycleData E W := ⟨2,![23,19,18,24],![18,38,26,39]⟩
def data673 : PartitionData E W := ⟨7,![cycle673_0,cycle673_1,cycle673_2,cycle673_3,cycle673_4,cycle673_5,cycle673_6]⟩
lemma valid_data673 : data673.Valid src673 dst673 Finset.univ := by decide +kernel

def src674 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,39,26,38,8,28,39,18,38]
def dst674 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,39,26,38,6,28,39,18,38,8]
def cycle674_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle674_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle674_2 : CycleData E W := ⟨3,![4,16,17,22,15],![4,6,16,39,28]⟩
def cycle674_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,38,18]⟩
def cycle674_4 : CycleData E W := ⟨2,![9,23,18,12],![14,18,39,26]⟩
def cycle674_5 : CycleData E W := ⟨3,![13,19,25,21,14],![5,26,38,8,28]⟩
def data674 : PartitionData E W := ⟨6,![cycle674_0,cycle674_1,cycle674_2,cycle674_3,cycle674_4,cycle674_5]⟩
lemma valid_data674 : data674.Valid src674 dst674 Finset.univ := by decide +kernel

def src675 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,39,26,38,8,38,18,28,39]
def dst675 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle675_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle675_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle675_2 : CycleData E W := ⟨3,![5,4,15,23,10],![2,6,4,28,18]⟩
def cycle675_3 : CycleData E W := ⟨2,![9,22,19,12],![14,18,38,26]⟩
def cycle675_4 : CycleData E W := ⟨2,![13,18,24,14],![5,26,39,28]⟩
def cycle675_5 : CycleData E W := ⟨3,![16,17,25,21,20],![6,16,39,8,38]⟩
def data675 : PartitionData E W := ⟨6,![cycle675_0,cycle675_1,cycle675_2,cycle675_3,cycle675_4,cycle675_5]⟩
lemma valid_data675 : data675.Valid src675 dst675 Finset.univ := by decide +kernel

def src676 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,39,26,38,8,38,28,18,39]
def dst676 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle676_0 : CycleData E W := ⟨2,![0,14,23,10],![2,5,28,18]⟩
def cycle676_1 : CycleData E W := ⟨2,![1,21,19,13],![5,8,38,26]⟩
def cycle676_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,39,16]⟩
def cycle676_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle676_4 : CycleData E W := ⟨2,![4,20,22,15],![4,6,38,28]⟩
def cycle676_5 : CycleData E W := ⟨1,![5,16,6],![2,6,16]⟩
def cycle676_6 : CycleData E W := ⟨2,![9,24,18,12],![14,18,39,26]⟩
def data676 : PartitionData E W := ⟨7,![cycle676_0,cycle676_1,cycle676_2,cycle676_3,cycle676_4,cycle676_5,cycle676_6]⟩
lemma valid_data676 : data676.Valid src676 dst676 Finset.univ := by decide +kernel

def src677 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,16,39,38,26,8,38,18,28,39]
def dst677 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,16,39,38,26,6,38,18,28,39,8]
def cycle677_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle677_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle677_2 : CycleData E W := ⟨3,![4,20,13,14,15],![4,6,26,5,28]⟩
def cycle677_3 : CycleData E W := ⟨4,![5,16,17,24,23,10],![2,6,16,39,28,18]⟩
def cycle677_4 : CycleData E W := ⟨2,![9,22,19,12],![14,18,38,26]⟩
def cycle677_5 : CycleData E W := ⟨1,![21,18,25],![8,38,39]⟩
def data677 : PartitionData E W := ⟨6,![cycle677_0,cycle677_1,cycle677_2,cycle677_3,cycle677_4,cycle677_5]⟩
lemma valid_data677 : data677.Valid src677 dst677 Finset.univ := by decide +kernel

def src678 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,16,38,39,8,38,28,18,39]
def dst678 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,16,38,39,6,38,28,18,39,8]
def cycle678_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle678_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle678_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle678_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle678_4 : CycleData E W := ⟨4,![9,23,22,18,17,12],![14,18,28,38,16,26]⟩
def cycle678_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data678 : PartitionData E W := ⟨6,![cycle678_0,cycle678_1,cycle678_2,cycle678_3,cycle678_4,cycle678_5]⟩
lemma valid_data678 : data678.Valid src678 dst678 Finset.univ := by decide +kernel

def src679 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,16,39,38,8,38,18,28,39]
def dst679 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,16,39,38,6,38,18,28,39,8]
def cycle679_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle679_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle679_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle679_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle679_4 : CycleData E W := ⟨4,![9,23,24,18,17,12],![14,18,28,39,16,26]⟩
def cycle679_5 : CycleData E W := ⟨1,![21,19,25],![8,38,39]⟩
def data679 : PartitionData E W := ⟨6,![cycle679_0,cycle679_1,cycle679_2,cycle679_3,cycle679_4,cycle679_5]⟩
lemma valid_data679 : data679.Valid src679 dst679 Finset.univ := by decide +kernel

def src680 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,38,16,39,8,18,38,28,39]
def dst680 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,38,16,39,6,18,38,28,39,8]
def cycle680_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle680_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle680_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle680_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle680_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle680_5 : CycleData E W := ⟨2,![18,23,24,19],![16,38,28,39]⟩
def data680 : PartitionData E W := ⟨6,![cycle680_0,cycle680_1,cycle680_2,cycle680_3,cycle680_4,cycle680_5]⟩
lemma valid_data680 : data680.Valid src680 dst680 Finset.univ := by decide +kernel

def src681 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,38,16,39,8,18,39,28,38]
def dst681 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,38,16,39,6,18,39,28,38,8]
def cycle681_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle681_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle681_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle681_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle681_4 : CycleData E W := ⟨3,![21,9,12,17,25],![8,18,14,26,38]⟩
def cycle681_5 : CycleData E W := ⟨2,![18,24,23,19],![16,38,28,39]⟩
def data681 : PartitionData E W := ⟨6,![cycle681_0,cycle681_1,cycle681_2,cycle681_3,cycle681_4,cycle681_5]⟩
lemma valid_data681 : data681.Valid src681 dst681 Finset.univ := by decide +kernel

def src682 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,38,16,39,8,38,18,28,39]
def dst682 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,38,16,39,6,38,18,28,39,8]
def cycle682_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle682_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle682_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle682_3 : CycleData E W := ⟨3,![5,20,24,23,10],![2,6,39,28,18]⟩
def cycle682_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle682_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data682 : PartitionData E W := ⟨6,![cycle682_0,cycle682_1,cycle682_2,cycle682_3,cycle682_4,cycle682_5]⟩
lemma valid_data682 : data682.Valid src682 dst682 Finset.univ := by decide +kernel

def src683 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,38,16,39,8,38,28,18,39]
def dst683 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,38,16,39,6,38,28,18,39,8]
def cycle683_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle683_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle683_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle683_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle683_4 : CycleData E W := ⟨3,![9,23,22,17,12],![14,18,28,38,26]⟩
def cycle683_5 : CycleData E W := ⟨2,![21,18,19,25],![8,38,16,39]⟩
def data683 : PartitionData E W := ⟨6,![cycle683_0,cycle683_1,cycle683_2,cycle683_3,cycle683_4,cycle683_5]⟩
lemma valid_data683 : data683.Valid src683 dst683 Finset.univ := by decide +kernel

def src684 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,39,16,38,8,18,38,28,39]
def dst684 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,39,16,38,6,18,38,28,39,8]
def cycle684_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle684_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle684_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle684_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle684_4 : CycleData E W := ⟨3,![21,9,12,17,25],![8,18,14,26,39]⟩
def cycle684_5 : CycleData E W := ⟨2,![18,24,23,19],![16,39,28,38]⟩
def data684 : PartitionData E W := ⟨6,![cycle684_0,cycle684_1,cycle684_2,cycle684_3,cycle684_4,cycle684_5]⟩
lemma valid_data684 : data684.Valid src684 dst684 Finset.univ := by decide +kernel

def src685 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,39,16,38,8,18,39,28,38]
def dst685 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,39,16,38,6,18,39,28,38,8]
def cycle685_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle685_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle685_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle685_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,38,8,18]⟩
def cycle685_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,39,26]⟩
def cycle685_5 : CycleData E W := ⟨2,![18,23,24,19],![16,39,28,38]⟩
def data685 : PartitionData E W := ⟨6,![cycle685_0,cycle685_1,cycle685_2,cycle685_3,cycle685_4,cycle685_5]⟩
lemma valid_data685 : data685.Valid src685 dst685 Finset.univ := by decide +kernel

def src686 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,39,16,38,8,38,18,28,39]
def dst686 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,39,16,38,6,38,18,28,39,8]
def cycle686_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle686_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle686_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle686_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,38,18]⟩
def cycle686_4 : CycleData E W := ⟨3,![9,23,24,17,12],![14,18,28,39,26]⟩
def cycle686_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data686 : PartitionData E W := ⟨6,![cycle686_0,cycle686_1,cycle686_2,cycle686_3,cycle686_4,cycle686_5]⟩
lemma valid_data686 : data686.Valid src686 dst686 Finset.univ := by decide +kernel

def src687 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,26,39,16,38,8,38,28,18,39]
def dst687 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,26,39,16,38,6,38,28,18,39,8]
def cycle687_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle687_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle687_2 : CycleData E W := ⟨3,![4,16,13,14,15],![4,6,26,5,28]⟩
def cycle687_3 : CycleData E W := ⟨3,![5,20,22,23,10],![2,6,38,28,18]⟩
def cycle687_4 : CycleData E W := ⟨2,![9,24,17,12],![14,18,39,26]⟩
def cycle687_5 : CycleData E W := ⟨2,![21,19,18,25],![8,38,16,39]⟩
def data687 : PartitionData E W := ⟨6,![cycle687_0,cycle687_1,cycle687_2,cycle687_3,cycle687_4,cycle687_5]⟩
lemma valid_data687 : data687.Valid src687 dst687 Finset.univ := by decide +kernel

def src688 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,18,28,38,39]
def dst688 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,18,28,38,39,8]
def cycle688_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle688_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle688_2 : CycleData E W := ⟨3,![5,4,15,22,10],![2,6,4,28,18]⟩
def cycle688_3 : CycleData E W := ⟨3,![21,9,12,19,25],![8,18,14,26,39]⟩
def cycle688_4 : CycleData E W := ⟨3,![13,18,17,23,14],![5,26,16,38,28]⟩
def cycle688_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data688 : PartitionData E W := ⟨6,![cycle688_0,cycle688_1,cycle688_2,cycle688_3,cycle688_4,cycle688_5]⟩
lemma valid_data688 : data688.Valid src688 dst688 Finset.univ := by decide +kernel

def src689 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,18,38,28,39]
def dst689 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle689_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle689_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle689_2 : CycleData E W := ⟨2,![4,16,23,15],![4,6,38,28]⟩
def cycle689_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle689_4 : CycleData E W := ⟨3,![9,22,17,18,12],![14,18,38,16,26]⟩
def cycle689_5 : CycleData E W := ⟨2,![13,19,24,14],![5,26,39,28]⟩
def data689 : PartitionData E W := ⟨6,![cycle689_0,cycle689_1,cycle689_2,cycle689_3,cycle689_4,cycle689_5]⟩
lemma valid_data689 : data689.Valid src689 dst689 Finset.univ := by decide +kernel

def src690 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,18,39,28,38]
def dst690 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle690_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle690_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle690_2 : CycleData E W := ⟨2,![4,20,23,15],![4,6,39,28]⟩
def cycle690_3 : CycleData E W := ⟨3,![5,16,25,21,10],![2,6,38,8,18]⟩
def cycle690_4 : CycleData E W := ⟨2,![9,22,19,12],![14,18,39,26]⟩
def cycle690_5 : CycleData E W := ⟨3,![13,18,17,24,14],![5,26,16,38,28]⟩
def data690 : PartitionData E W := ⟨6,![cycle690_0,cycle690_1,cycle690_2,cycle690_3,cycle690_4,cycle690_5]⟩
lemma valid_data690 : data690.Valid src690 dst690 Finset.univ := by decide +kernel

def src691 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,18,39,38,28]
def dst691 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,18,39,38,28,8]
def cycle691_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle691_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle691_2 : CycleData E W := ⟨2,![4,16,24,15],![4,6,38,28]⟩
def cycle691_3 : CycleData E W := ⟨2,![5,20,22,10],![2,6,39,18]⟩
def cycle691_4 : CycleData E W := ⟨4,![13,12,9,21,25,14],![5,26,14,18,8,28]⟩
def cycle691_5 : CycleData E W := ⟨2,![17,23,19,18],![16,38,39,26]⟩
def data691 : PartitionData E W := ⟨6,![cycle691_0,cycle691_1,cycle691_2,cycle691_3,cycle691_4,cycle691_5]⟩
lemma valid_data691 : data691.Valid src691 dst691 Finset.univ := by decide +kernel

def src692 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,28,18,39,38]
def dst692 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,28,18,39,38,8]
def cycle692_0 : CycleData E W := ⟨2,![0,13,18,6],![2,5,26,16]⟩
def cycle692_1 : CycleData E W := ⟨1,![1,21,14],![5,8,28]⟩
def cycle692_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,38,16]⟩
def cycle692_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle692_4 : CycleData E W := ⟨3,![5,4,15,22,10],![2,6,4,28,18]⟩
def cycle692_5 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def cycle692_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data692 : PartitionData E W := ⟨7,![cycle692_0,cycle692_1,cycle692_2,cycle692_3,cycle692_4,cycle692_5,cycle692_6]⟩
lemma valid_data692 : data692.Valid src692 dst692 Finset.univ := by decide +kernel

def src693 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,28,38,18,39]
def dst693 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,28,38,18,39,8]
def cycle693_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle693_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle693_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle693_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle693_4 : CycleData E W := ⟨3,![9,23,17,18,12],![14,18,38,16,26]⟩
def cycle693_5 : CycleData E W := ⟨3,![13,19,25,21,14],![5,26,39,8,28]⟩
def data693 : PartitionData E W := ⟨6,![cycle693_0,cycle693_1,cycle693_2,cycle693_3,cycle693_4,cycle693_5]⟩
lemma valid_data693 : data693.Valid src693 dst693 Finset.univ := by decide +kernel

def src694 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,28,39,18,38]
def dst694 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,28,39,18,38,8]
def cycle694_0 : CycleData E W := ⟨2,![0,13,18,6],![2,5,26,16]⟩
def cycle694_1 : CycleData E W := ⟨1,![1,21,14],![5,8,28]⟩
def cycle694_2 : CycleData E W := ⟨2,![2,25,17,7],![3,8,38,16]⟩
def cycle694_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle694_4 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle694_5 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle694_6 : CycleData E W := ⟨2,![9,23,19,12],![14,18,39,26]⟩
def data694 : PartitionData E W := ⟨7,![cycle694_0,cycle694_1,cycle694_2,cycle694_3,cycle694_4,cycle694_5,cycle694_6]⟩
lemma valid_data694 : data694.Valid src694 dst694 Finset.univ := by decide +kernel

def src695 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst695 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle695_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle695_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle695_2 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle695_3 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle695_4 : CycleData E W := ⟨3,![13,12,9,23,14],![5,26,14,18,28]⟩
def cycle695_5 : CycleData E W := ⟨3,![21,17,18,19,25],![8,38,16,26,39]⟩
def data695 : PartitionData E W := ⟨6,![cycle695_0,cycle695_1,cycle695_2,cycle695_3,cycle695_4,cycle695_5]⟩
lemma valid_data695 : data695.Valid src695 dst695 Finset.univ := by decide +kernel

def src696 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,18,28,39,38]
def dst696 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,18,28,39,38,8]
def cycle696_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle696_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle696_2 : CycleData E W := ⟨3,![5,4,15,22,10],![2,6,4,28,18]⟩
def cycle696_3 : CycleData E W := ⟨3,![21,9,12,17,25],![8,18,14,26,38]⟩
def cycle696_4 : CycleData E W := ⟨3,![13,18,19,23,14],![5,26,16,39,28]⟩
def cycle696_5 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data696 : PartitionData E W := ⟨6,![cycle696_0,cycle696_1,cycle696_2,cycle696_3,cycle696_4,cycle696_5]⟩
lemma valid_data696 : data696.Valid src696 dst696 Finset.univ := by decide +kernel

def src697 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,18,38,28,39]
def dst697 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle697_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle697_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle697_2 : CycleData E W := ⟨2,![4,16,23,15],![4,6,38,28]⟩
def cycle697_3 : CycleData E W := ⟨3,![5,20,25,21,10],![2,6,39,8,18]⟩
def cycle697_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle697_5 : CycleData E W := ⟨3,![13,18,19,24,14],![5,26,16,39,28]⟩
def data697 : PartitionData E W := ⟨6,![cycle697_0,cycle697_1,cycle697_2,cycle697_3,cycle697_4,cycle697_5]⟩
lemma valid_data697 : data697.Valid src697 dst697 Finset.univ := by decide +kernel

def src698 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,18,38,39,28]
def dst698 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,18,38,39,28,8]
def cycle698_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle698_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle698_2 : CycleData E W := ⟨2,![4,20,24,15],![4,6,39,28]⟩
def cycle698_3 : CycleData E W := ⟨2,![5,16,22,10],![2,6,38,18]⟩
def cycle698_4 : CycleData E W := ⟨4,![13,12,9,21,25,14],![5,26,14,18,8,28]⟩
def cycle698_5 : CycleData E W := ⟨2,![18,17,23,19],![16,26,38,39]⟩
def data698 : PartitionData E W := ⟨6,![cycle698_0,cycle698_1,cycle698_2,cycle698_3,cycle698_4,cycle698_5]⟩
lemma valid_data698 : data698.Valid src698 dst698 Finset.univ := by decide +kernel

def src699 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,18,39,28,38]
def dst699 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle699_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle699_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle699_2 : CycleData E W := ⟨2,![4,20,23,15],![4,6,39,28]⟩
def cycle699_3 : CycleData E W := ⟨3,![5,16,25,21,10],![2,6,38,8,18]⟩
def cycle699_4 : CycleData E W := ⟨3,![9,22,19,18,12],![14,18,39,16,26]⟩
def cycle699_5 : CycleData E W := ⟨2,![13,17,24,14],![5,26,38,28]⟩
def data699 : PartitionData E W := ⟨6,![cycle699_0,cycle699_1,cycle699_2,cycle699_3,cycle699_4,cycle699_5]⟩
lemma valid_data699 : data699.Valid src699 dst699 Finset.univ := by decide +kernel

def lookupB13 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data650 else (if j < 2 then data651 else data652)) else (if j < 4 then data653 else (if j < 5 then data654 else data655))) else (if j < 9 then (if j < 7 then data656 else (if j < 8 then data657 else data658)) else (if j < 10 then data659 else (if j < 11 then data660 else data661)))) else (if j < 18 then (if j < 15 then (if j < 13 then data662 else (if j < 14 then data663 else data664)) else (if j < 16 then data665 else (if j < 17 then data666 else data667))) else (if j < 21 then (if j < 19 then data668 else (if j < 20 then data669 else data670)) else (if j < 23 then (if j < 22 then data671 else data672) else (if j < 24 then data673 else data674))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data675 else (if j < 27 then data676 else data677)) else (if j < 29 then data678 else (if j < 30 then data679 else data680))) else (if j < 34 then (if j < 32 then data681 else (if j < 33 then data682 else data683)) else (if j < 35 then data684 else (if j < 36 then data685 else data686)))) else (if j < 43 then (if j < 40 then (if j < 38 then data687 else (if j < 39 then data688 else data689)) else (if j < 41 then data690 else (if j < 42 then data691 else data692))) else (if j < 46 then (if j < 44 then data693 else (if j < 45 then data694 else data695)) else (if j < 48 then (if j < 47 then data696 else data697) else (if j < 49 then data698 else data699))))))

def srcTableB13 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src650 else (if j < 2 then src651 else src652)) else (if j < 4 then src653 else (if j < 5 then src654 else src655))) else (if j < 9 then (if j < 7 then src656 else (if j < 8 then src657 else src658)) else (if j < 10 then src659 else (if j < 11 then src660 else src661)))) else (if j < 18 then (if j < 15 then (if j < 13 then src662 else (if j < 14 then src663 else src664)) else (if j < 16 then src665 else (if j < 17 then src666 else src667))) else (if j < 21 then (if j < 19 then src668 else (if j < 20 then src669 else src670)) else (if j < 23 then (if j < 22 then src671 else src672) else (if j < 24 then src673 else src674))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src675 else (if j < 27 then src676 else src677)) else (if j < 29 then src678 else (if j < 30 then src679 else src680))) else (if j < 34 then (if j < 32 then src681 else (if j < 33 then src682 else src683)) else (if j < 35 then src684 else (if j < 36 then src685 else src686)))) else (if j < 43 then (if j < 40 then (if j < 38 then src687 else (if j < 39 then src688 else src689)) else (if j < 41 then src690 else (if j < 42 then src691 else src692))) else (if j < 46 then (if j < 44 then src693 else (if j < 45 then src694 else src695)) else (if j < 48 then (if j < 47 then src696 else src697) else (if j < 49 then src698 else src699))))))

def dstTableB13 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst650 else (if j < 2 then dst651 else dst652)) else (if j < 4 then dst653 else (if j < 5 then dst654 else dst655))) else (if j < 9 then (if j < 7 then dst656 else (if j < 8 then dst657 else dst658)) else (if j < 10 then dst659 else (if j < 11 then dst660 else dst661)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst662 else (if j < 14 then dst663 else dst664)) else (if j < 16 then dst665 else (if j < 17 then dst666 else dst667))) else (if j < 21 then (if j < 19 then dst668 else (if j < 20 then dst669 else dst670)) else (if j < 23 then (if j < 22 then dst671 else dst672) else (if j < 24 then dst673 else dst674))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst675 else (if j < 27 then dst676 else dst677)) else (if j < 29 then dst678 else (if j < 30 then dst679 else dst680))) else (if j < 34 then (if j < 32 then dst681 else (if j < 33 then dst682 else dst683)) else (if j < 35 then dst684 else (if j < 36 then dst685 else dst686)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst687 else (if j < 39 then dst688 else dst689)) else (if j < 41 then dst690 else (if j < 42 then dst691 else dst692))) else (if j < 46 then (if j < 44 then dst693 else (if j < 45 then dst694 else dst695)) else (if j < 48 then (if j < 47 then dst696 else dst697) else (if j < 49 then dst698 else dst699))))))

def caseB13 (i : Fin 50) : Cases := ⟨650 + i.val,by have := i.isLt; omega⟩
lemma tableB13_valid (i : Fin 50) :
    (lookupB13 i.val).Valid (srcTableB13 i.val) (dstTableB13 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB13_row : ∀ (i : Fin 50) (e : E),
    srcTableB13 i.val e = caseSource (caseB13 i) e := by decide +kernel

lemma dstB13_row : ∀ (i : Fin 50) (e : E),
    dstTableB13 i.val e = caseTarget (caseB13 i) e := by decide +kernel

lemma sizeB13 : ∀ i : Fin 50, (lookupB13 i.val).size ≤ 5 →
    (lookupB13 i.val).size = 2 ∧
      (⟨caseKey (caseB13 i),caseKey_lt (caseB13 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB13 (i : Fin 50) : Certificate (caseB13 i) := by
  refine ⟨lookupB13 i.val,?_,sizeB13 i⟩
  have hv := tableB13_valid i
  rw [funext (srcB13_row i),funext (dstB13_row i)] at hv
  exact hv
lemma certificateInterval13 : FiniteIntervals.Covers CertificateAt 650 700 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 650 50 (fun i _ => certificateB13 i)
#print axioms certificateInterval13
end Erdos184Work.FiveRows4

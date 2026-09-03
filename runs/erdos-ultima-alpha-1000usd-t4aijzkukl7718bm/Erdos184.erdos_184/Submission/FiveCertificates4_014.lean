import Submission.FiveCertificates4Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows4
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src700 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,28,18,38,39]
def dst700 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,28,18,38,39,8]
def cycle700_0 : CycleData E W := ⟨2,![0,13,18,6],![2,5,26,16]⟩
def cycle700_1 : CycleData E W := ⟨1,![1,21,14],![5,8,28]⟩
def cycle700_2 : CycleData E W := ⟨2,![2,25,19,7],![3,8,39,16]⟩
def cycle700_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle700_4 : CycleData E W := ⟨3,![5,4,15,22,10],![2,6,4,28,18]⟩
def cycle700_5 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def cycle700_6 : CycleData E W := ⟨1,![16,24,20],![6,38,39]⟩
def data700 : PartitionData E W := ⟨7,![cycle700_0,cycle700_1,cycle700_2,cycle700_3,cycle700_4,cycle700_5,cycle700_6]⟩
lemma valid_data700 : data700.Valid src700 dst700 Finset.univ := by decide +kernel

def src701 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,28,38,18,39]
def dst701 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,28,38,18,39,8]
def cycle701_0 : CycleData E W := ⟨2,![0,13,18,6],![2,5,26,16]⟩
def cycle701_1 : CycleData E W := ⟨1,![1,21,14],![5,8,28]⟩
def cycle701_2 : CycleData E W := ⟨2,![2,25,19,7],![3,8,39,16]⟩
def cycle701_3 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle701_4 : CycleData E W := ⟨2,![4,16,22,15],![4,6,38,28]⟩
def cycle701_5 : CycleData E W := ⟨2,![5,20,24,10],![2,6,39,18]⟩
def cycle701_6 : CycleData E W := ⟨2,![9,23,17,12],![14,18,38,26]⟩
def data701 : PartitionData E W := ⟨7,![cycle701_0,cycle701_1,cycle701_2,cycle701_3,cycle701_4,cycle701_5,cycle701_6]⟩
lemma valid_data701 : data701.Valid src701 dst701 Finset.univ := by decide +kernel

def src702 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,28,39,18,38]
def dst702 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,28,39,18,38,8]
def cycle702_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle702_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle702_2 : CycleData E W := ⟨2,![4,20,22,15],![4,6,39,28]⟩
def cycle702_3 : CycleData E W := ⟨2,![5,16,24,10],![2,6,38,18]⟩
def cycle702_4 : CycleData E W := ⟨3,![9,23,19,18,12],![14,18,39,16,26]⟩
def cycle702_5 : CycleData E W := ⟨3,![13,17,25,21,14],![5,26,38,8,28]⟩
def data702 : PartitionData E W := ⟨6,![cycle702_0,cycle702_1,cycle702_2,cycle702_3,cycle702_4,cycle702_5]⟩
lemma valid_data702 : data702.Valid src702 dst702 Finset.univ := by decide +kernel

def src703 : E → W := ![2,5,8,3,4,6,2,16,3,14,18,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst703 : E → W := ![5,8,3,4,6,2,16,3,14,18,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle703_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,5,8,3,16]⟩
def cycle703_1 : CycleData E W := ⟨1,![3,11,8],![3,4,14]⟩
def cycle703_2 : CycleData E W := ⟨3,![5,4,15,23,10],![2,6,4,28,18]⟩
def cycle703_3 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle703_4 : CycleData E W := ⟨3,![13,18,19,24,14],![5,26,16,39,28]⟩
def cycle703_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data703 : PartitionData E W := ⟨6,![cycle703_0,cycle703_1,cycle703_2,cycle703_3,cycle703_4,cycle703_5]⟩
lemma valid_data703 : data703.Valid src703 dst703 Finset.univ := by decide +kernel

def src704 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst704 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle704_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle704_1 : CycleData E W := ⟨2,![3,13,18,7],![3,5,26,16]⟩
def cycle704_2 : CycleData E W := ⟨4,![5,4,14,15,11,10],![2,8,5,28,4,14]⟩
def cycle704_3 : CycleData E W := ⟨2,![8,23,22,17],![16,18,28,38]⟩
def cycle704_4 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle704_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data704 : PartitionData E W := ⟨6,![cycle704_0,cycle704_1,cycle704_2,cycle704_3,cycle704_4,cycle704_5]⟩
lemma valid_data704 : data704.Valid src704 dst704 Finset.univ := by decide +kernel

def src705 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst705 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle705_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle705_1 : CycleData E W := ⟨2,![3,13,18,7],![3,5,26,16]⟩
def cycle705_2 : CycleData E W := ⟨4,![5,4,14,15,11,10],![2,8,5,28,4,14]⟩
def cycle705_3 : CycleData E W := ⟨2,![8,23,24,19],![16,18,28,39]⟩
def cycle705_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle705_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data705 : PartitionData E W := ⟨6,![cycle705_0,cycle705_1,cycle705_2,cycle705_3,cycle705_4,cycle705_5]⟩
lemma valid_data705 : data705.Valid src705 dst705 Finset.univ := by decide +kernel

def src706 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst706 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle706_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle706_1 : CycleData E W := ⟨2,![3,12,18,7],![3,5,26,16]⟩
def cycle706_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle706_3 : CycleData E W := ⟨3,![9,8,17,22,14],![14,18,16,38,28]⟩
def cycle706_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle706_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data706 : PartitionData E W := ⟨6,![cycle706_0,cycle706_1,cycle706_2,cycle706_3,cycle706_4,cycle706_5]⟩
lemma valid_data706 : data706.Valid src706 dst706 Finset.univ := by decide +kernel

def src707 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst707 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle707_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle707_1 : CycleData E W := ⟨2,![3,12,18,7],![3,5,26,16]⟩
def cycle707_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle707_3 : CycleData E W := ⟨3,![16,22,8,19,20],![6,38,18,16,39]⟩
def cycle707_4 : CycleData E W := ⟨1,![9,23,14],![14,18,28]⟩
def cycle707_5 : CycleData E W := ⟨4,![11,17,21,25,24,15],![4,26,38,8,39,28]⟩
def data707 : PartitionData E W := ⟨6,![cycle707_0,cycle707_1,cycle707_2,cycle707_3,cycle707_4,cycle707_5]⟩
lemma valid_data707 : data707.Valid src707 dst707 Finset.univ := by decide +kernel

def src708 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst708 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle708_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle708_1 : CycleData E W := ⟨2,![3,14,23,7],![3,5,28,18]⟩
def cycle708_2 : CycleData E W := ⟨3,![5,4,13,12,10],![2,8,5,26,14]⟩
def cycle708_3 : CycleData E W := ⟨2,![8,24,19,18],![16,18,39,26]⟩
def cycle708_4 : CycleData E W := ⟨3,![11,9,17,22,15],![4,14,16,38,28]⟩
def cycle708_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data708 : PartitionData E W := ⟨6,![cycle708_0,cycle708_1,cycle708_2,cycle708_3,cycle708_4,cycle708_5]⟩
lemma valid_data708 : data708.Valid src708 dst708 Finset.univ := by decide +kernel

def src709 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst709 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle709_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle709_1 : CycleData E W := ⟨3,![3,13,17,22,7],![3,5,26,38,18]⟩
def cycle709_2 : CycleData E W := ⟨4,![5,4,14,15,11,10],![2,8,5,28,4,14]⟩
def cycle709_3 : CycleData E W := ⟨2,![8,23,24,19],![16,18,28,39]⟩
def cycle709_4 : CycleData E W := ⟨1,![9,18,12],![14,16,26]⟩
def cycle709_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data709 : PartitionData E W := ⟨6,![cycle709_0,cycle709_1,cycle709_2,cycle709_3,cycle709_4,cycle709_5]⟩
lemma valid_data709 : data709.Valid src709 dst709 Finset.univ := by decide +kernel

def src710 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst710 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle710_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle710_1 : CycleData E W := ⟨3,![3,12,18,8,7],![3,5,26,16,18]⟩
def cycle710_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle710_3 : CycleData E W := ⟨2,![9,17,22,14],![14,16,38,28]⟩
def cycle710_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle710_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data710 : PartitionData E W := ⟨6,![cycle710_0,cycle710_1,cycle710_2,cycle710_3,cycle710_4,cycle710_5]⟩
lemma valid_data710 : data710.Valid src710 dst710 Finset.univ := by decide +kernel

def src711 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst711 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle711_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle711_1 : CycleData E W := ⟨3,![3,12,18,8,7],![3,5,26,16,18]⟩
def cycle711_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle711_3 : CycleData E W := ⟨2,![9,19,24,14],![14,16,39,28]⟩
def cycle711_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle711_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data711 : PartitionData E W := ⟨6,![cycle711_0,cycle711_1,cycle711_2,cycle711_3,cycle711_4,cycle711_5]⟩
lemma valid_data711 : data711.Valid src711 dst711 Finset.univ := by decide +kernel

def src712 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,39,8,38,18,28,39]
def dst712 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle712_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle712_1 : CycleData E W := ⟨2,![1,20,19,11],![4,6,39,26]⟩
def cycle712_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle712_3 : CycleData E W := ⟨2,![4,21,18,12],![5,8,38,26]⟩
def cycle712_4 : CycleData E W := ⟨3,![5,25,24,23,10],![2,8,39,28,18]⟩
def cycle712_5 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def data712 : PartitionData E W := ⟨6,![cycle712_0,cycle712_1,cycle712_2,cycle712_3,cycle712_4,cycle712_5]⟩
lemma valid_data712 : data712.Valid src712 dst712 Finset.univ := by decide +kernel

def src713 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,39,8,38,28,18,39]
def dst713 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle713_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle713_1 : CycleData E W := ⟨2,![1,20,19,11],![4,6,39,26]⟩
def cycle713_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle713_3 : CycleData E W := ⟨2,![4,21,18,12],![5,8,38,26]⟩
def cycle713_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle713_5 : CycleData E W := ⟨3,![8,17,22,23,9],![3,16,38,28,18]⟩
def data713 : PartitionData E W := ⟨6,![cycle713_0,cycle713_1,cycle713_2,cycle713_3,cycle713_4,cycle713_5]⟩
lemma valid_data713 : data713.Valid src713 dst713 Finset.univ := by decide +kernel

def src714 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,39,26,38,8,38,18,28,39]
def dst714 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle714_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle714_1 : CycleData E W := ⟨2,![1,20,19,11],![4,6,38,26]⟩
def cycle714_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle714_3 : CycleData E W := ⟨2,![4,25,18,12],![5,8,39,26]⟩
def cycle714_4 : CycleData E W := ⟨2,![5,21,22,10],![2,8,38,18]⟩
def cycle714_5 : CycleData E W := ⟨3,![8,17,24,23,9],![3,16,39,28,18]⟩
def data714 : PartitionData E W := ⟨6,![cycle714_0,cycle714_1,cycle714_2,cycle714_3,cycle714_4,cycle714_5]⟩
lemma valid_data714 : data714.Valid src714 dst714 Finset.univ := by decide +kernel

def src715 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,39,26,38,8,38,28,18,39]
def dst715 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle715_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle715_1 : CycleData E W := ⟨2,![1,20,19,11],![4,6,38,26]⟩
def cycle715_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle715_3 : CycleData E W := ⟨2,![4,25,18,12],![5,8,39,26]⟩
def cycle715_4 : CycleData E W := ⟨3,![5,21,22,23,10],![2,8,38,28,18]⟩
def cycle715_5 : CycleData E W := ⟨2,![8,17,24,9],![3,16,39,18]⟩
def data715 : PartitionData E W := ⟨6,![cycle715_0,cycle715_1,cycle715_2,cycle715_3,cycle715_4,cycle715_5]⟩
lemma valid_data715 : data715.Valid src715 dst715 Finset.univ := by decide +kernel

def src716 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,18,38,28,39]
def dst716 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle716_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,4,3,18]⟩
def cycle716_1 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle716_2 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle716_3 : CycleData E W := ⟨2,![7,17,23,14],![14,16,38,28]⟩
def cycle716_4 : CycleData E W := ⟨2,![11,19,24,15],![4,26,39,28]⟩
def cycle716_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data716 : PartitionData E W := ⟨6,![cycle716_0,cycle716_1,cycle716_2,cycle716_3,cycle716_4,cycle716_5]⟩
lemma valid_data716 : data716.Valid src716 dst716 Finset.univ := by decide +kernel

def src717 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,18,39,28,38]
def dst717 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle717_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,4,3,18]⟩
def cycle717_1 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle717_2 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle717_3 : CycleData E W := ⟨2,![7,17,24,14],![14,16,38,28]⟩
def cycle717_4 : CycleData E W := ⟨2,![11,19,23,15],![4,26,39,28]⟩
def cycle717_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data717 : PartitionData E W := ⟨6,![cycle717_0,cycle717_1,cycle717_2,cycle717_3,cycle717_4,cycle717_5]⟩
lemma valid_data717 : data717.Valid src717 dst717 Finset.univ := by decide +kernel

def src718 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,38,16,26,39,8,38,28,18,39]
def dst718 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle718_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,4,3,18]⟩
def cycle718_1 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle718_2 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle718_3 : CycleData E W := ⟨2,![7,17,22,14],![14,16,38,28]⟩
def cycle718_4 : CycleData E W := ⟨3,![11,19,24,23,15],![4,26,39,18,28]⟩
def cycle718_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data718 : PartitionData E W := ⟨6,![cycle718_0,cycle718_1,cycle718_2,cycle718_3,cycle718_4,cycle718_5]⟩
lemma valid_data718 : data718.Valid src718 dst718 Finset.univ := by decide +kernel

def src719 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,18,38,28,39]
def dst719 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle719_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,4,3,18]⟩
def cycle719_1 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle719_2 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle719_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle719_4 : CycleData E W := ⟨2,![11,17,23,15],![4,26,38,28]⟩
def cycle719_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data719 : PartitionData E W := ⟨6,![cycle719_0,cycle719_1,cycle719_2,cycle719_3,cycle719_4,cycle719_5]⟩
lemma valid_data719 : data719.Valid src719 dst719 Finset.univ := by decide +kernel

def src720 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,18,39,28,38]
def dst720 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle720_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,4,3,18]⟩
def cycle720_1 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle720_2 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle720_3 : CycleData E W := ⟨2,![7,19,23,14],![14,16,39,28]⟩
def cycle720_4 : CycleData E W := ⟨2,![11,17,24,15],![4,26,38,28]⟩
def cycle720_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data720 : PartitionData E W := ⟨6,![cycle720_0,cycle720_1,cycle720_2,cycle720_3,cycle720_4,cycle720_5]⟩
lemma valid_data720 : data720.Valid src720 dst720 Finset.univ := by decide +kernel

def src721 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,38,26,16,39,8,38,18,28,39]
def dst721 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle721_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,4,3,18]⟩
def cycle721_1 : CycleData E W := ⟨2,![3,12,18,8],![3,5,26,16]⟩
def cycle721_2 : CycleData E W := ⟨2,![5,4,13,6],![2,8,5,14]⟩
def cycle721_3 : CycleData E W := ⟨2,![7,19,24,14],![14,16,39,28]⟩
def cycle721_4 : CycleData E W := ⟨3,![11,17,22,23,15],![4,26,38,18,28]⟩
def cycle721_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data721 : PartitionData E W := ⟨6,![cycle721_0,cycle721_1,cycle721_2,cycle721_3,cycle721_4,cycle721_5]⟩
lemma valid_data721 : data721.Valid src721 dst721 Finset.univ := by decide +kernel

def src722 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,39,8,38,18,28,39]
def dst722 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,39,6,38,18,28,39,8]
def cycle722_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle722_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle722_2 : CycleData E W := ⟨2,![4,21,18,13],![5,8,38,26]⟩
def cycle722_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle722_4 : CycleData E W := ⟨3,![7,23,24,19,12],![14,18,28,39,26]⟩
def cycle722_5 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def data722 : PartitionData E W := ⟨6,![cycle722_0,cycle722_1,cycle722_2,cycle722_3,cycle722_4,cycle722_5]⟩
lemma valid_data722 : data722.Valid src722 dst722 Finset.univ := by decide +kernel

def src723 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,39,8,38,28,18,39]
def dst723 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,39,6,38,28,18,39,8]
def cycle723_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle723_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle723_2 : CycleData E W := ⟨2,![4,21,18,13],![5,8,38,26]⟩
def cycle723_3 : CycleData E W := ⟨3,![5,25,20,16,10],![2,8,39,6,16]⟩
def cycle723_4 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle723_5 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def data723 : PartitionData E W := ⟨6,![cycle723_0,cycle723_1,cycle723_2,cycle723_3,cycle723_4,cycle723_5]⟩
lemma valid_data723 : data723.Valid src723 dst723 Finset.univ := by decide +kernel

def src724 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,39,26,38,8,38,18,28,39]
def dst724 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,39,26,38,6,38,18,28,39,8]
def cycle724_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle724_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle724_2 : CycleData E W := ⟨2,![4,21,19,13],![5,8,38,26]⟩
def cycle724_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle724_4 : CycleData E W := ⟨3,![7,23,24,18,12],![14,18,28,39,26]⟩
def cycle724_5 : CycleData E W := ⟨3,![8,22,20,16,9],![3,18,38,6,16]⟩
def data724 : PartitionData E W := ⟨6,![cycle724_0,cycle724_1,cycle724_2,cycle724_3,cycle724_4,cycle724_5]⟩
lemma valid_data724 : data724.Valid src724 dst724 Finset.univ := by decide +kernel

def src725 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,39,26,38,8,38,28,18,39]
def dst725 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,39,26,38,6,38,28,18,39,8]
def cycle725_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle725_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle725_2 : CycleData E W := ⟨2,![4,21,19,13],![5,8,38,26]⟩
def cycle725_3 : CycleData E W := ⟨2,![5,25,17,10],![2,8,39,16]⟩
def cycle725_4 : CycleData E W := ⟨2,![7,24,18,12],![14,18,39,26]⟩
def cycle725_5 : CycleData E W := ⟨4,![8,23,22,20,16,9],![3,18,28,38,6,16]⟩
def data725 : PartitionData E W := ⟨6,![cycle725_0,cycle725_1,cycle725_2,cycle725_3,cycle725_4,cycle725_5]⟩
lemma valid_data725 : data725.Valid src725 dst725 Finset.univ := by decide +kernel

def src726 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,18,38,28,39]
def dst726 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,18,38,28,39,8]
def cycle726_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle726_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle726_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle726_3 : CycleData E W := ⟨3,![21,7,12,19,25],![8,18,14,26,39]⟩
def cycle726_4 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def cycle726_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data726 : PartitionData E W := ⟨6,![cycle726_0,cycle726_1,cycle726_2,cycle726_3,cycle726_4,cycle726_5]⟩
lemma valid_data726 : data726.Valid src726 dst726 Finset.univ := by decide +kernel

def src727 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,18,39,28,38]
def dst727 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,18,39,28,38,8]
def cycle727_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle727_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle727_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle727_3 : CycleData E W := ⟨2,![7,22,19,12],![14,18,39,26]⟩
def cycle727_4 : CycleData E W := ⟨3,![8,21,25,17,9],![3,18,8,38,16]⟩
def cycle727_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data727 : PartitionData E W := ⟨6,![cycle727_0,cycle727_1,cycle727_2,cycle727_3,cycle727_4,cycle727_5]⟩
lemma valid_data727 : data727.Valid src727 dst727 Finset.univ := by decide +kernel

def src728 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,16,26,39,8,38,28,18,39]
def dst728 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle728_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle728_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle728_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle728_3 : CycleData E W := ⟨2,![7,24,19,12],![14,18,39,26]⟩
def cycle728_4 : CycleData E W := ⟨3,![8,23,22,17,9],![3,18,28,38,16]⟩
def cycle728_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data728 : PartitionData E W := ⟨6,![cycle728_0,cycle728_1,cycle728_2,cycle728_3,cycle728_4,cycle728_5]⟩
lemma valid_data728 : data728.Valid src728 dst728 Finset.univ := by decide +kernel

def src729 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,18,38,28,39]
def dst729 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,18,38,28,39,8]
def cycle729_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle729_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle729_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle729_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle729_4 : CycleData E W := ⟨3,![8,21,25,19,9],![3,18,8,39,16]⟩
def cycle729_5 : CycleData E W := ⟨2,![16,23,24,20],![6,38,28,39]⟩
def data729 : PartitionData E W := ⟨6,![cycle729_0,cycle729_1,cycle729_2,cycle729_3,cycle729_4,cycle729_5]⟩
lemma valid_data729 : data729.Valid src729 dst729 Finset.univ := by decide +kernel

def src730 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,18,39,28,38]
def dst730 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,18,39,28,38,8]
def cycle730_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle730_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle730_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle730_3 : CycleData E W := ⟨3,![21,7,12,17,25],![8,18,14,26,38]⟩
def cycle730_4 : CycleData E W := ⟨2,![8,22,19,9],![3,18,39,16]⟩
def cycle730_5 : CycleData E W := ⟨2,![16,24,23,20],![6,38,28,39]⟩
def data730 : PartitionData E W := ⟨6,![cycle730_0,cycle730_1,cycle730_2,cycle730_3,cycle730_4,cycle730_5]⟩
lemma valid_data730 : data730.Valid src730 dst730 Finset.univ := by decide +kernel

def src731 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,38,26,16,39,8,38,18,28,39]
def dst731 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle731_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle731_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle731_2 : CycleData E W := ⟨3,![5,4,13,18,10],![2,8,5,26,16]⟩
def cycle731_3 : CycleData E W := ⟨2,![7,22,17,12],![14,18,38,26]⟩
def cycle731_4 : CycleData E W := ⟨3,![8,23,24,19,9],![3,18,28,39,16]⟩
def cycle731_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data731 : PartitionData E W := ⟨6,![cycle731_0,cycle731_1,cycle731_2,cycle731_3,cycle731_4,cycle731_5]⟩
lemma valid_data731 : data731.Valid src731 dst731 Finset.univ := by decide +kernel

def src732 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst732 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle732_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle732_1 : CycleData E W := ⟨2,![3,15,18,7],![3,4,26,16]⟩
def cycle732_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle732_3 : CycleData E W := ⟨3,![9,8,17,22,12],![14,18,16,38,28]⟩
def cycle732_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle732_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data732 : PartitionData E W := ⟨6,![cycle732_0,cycle732_1,cycle732_2,cycle732_3,cycle732_4,cycle732_5]⟩
lemma valid_data732 : data732.Valid src732 dst732 Finset.univ := by decide +kernel

def src733 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst733 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle733_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle733_1 : CycleData E W := ⟨2,![3,15,18,7],![3,4,26,16]⟩
def cycle733_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle733_3 : CycleData E W := ⟨3,![16,22,8,19,20],![6,38,18,16,39]⟩
def cycle733_4 : CycleData E W := ⟨1,![9,23,12],![14,18,28]⟩
def cycle733_5 : CycleData E W := ⟨4,![13,24,25,21,17,14],![5,28,39,8,38,26]⟩
def data733 : PartitionData E W := ⟨6,![cycle733_0,cycle733_1,cycle733_2,cycle733_3,cycle733_4,cycle733_5]⟩
lemma valid_data733 : data733.Valid src733 dst733 Finset.univ := by decide +kernel

def src734 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst734 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle734_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle734_1 : CycleData E W := ⟨2,![3,11,18,7],![3,4,26,16]⟩
def cycle734_2 : CycleData E W := ⟨4,![5,4,15,14,13,10],![2,8,4,28,5,14]⟩
def cycle734_3 : CycleData E W := ⟨2,![8,23,22,17],![16,18,28,38]⟩
def cycle734_4 : CycleData E W := ⟨2,![9,24,19,12],![14,18,39,26]⟩
def cycle734_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data734 : PartitionData E W := ⟨6,![cycle734_0,cycle734_1,cycle734_2,cycle734_3,cycle734_4,cycle734_5]⟩
lemma valid_data734 : data734.Valid src734 dst734 Finset.univ := by decide +kernel

def src735 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst735 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle735_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle735_1 : CycleData E W := ⟨2,![3,11,18,7],![3,4,26,16]⟩
def cycle735_2 : CycleData E W := ⟨4,![5,4,15,14,13,10],![2,8,4,28,5,14]⟩
def cycle735_3 : CycleData E W := ⟨2,![8,23,24,19],![16,18,28,39]⟩
def cycle735_4 : CycleData E W := ⟨2,![9,22,17,12],![14,18,38,26]⟩
def cycle735_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data735 : PartitionData E W := ⟨6,![cycle735_0,cycle735_1,cycle735_2,cycle735_3,cycle735_4,cycle735_5]⟩
lemma valid_data735 : data735.Valid src735 dst735 Finset.univ := by decide +kernel

def src736 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst736 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle736_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle736_1 : CycleData E W := ⟨3,![3,15,18,8,7],![3,4,26,16,18]⟩
def cycle736_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle736_3 : CycleData E W := ⟨2,![9,17,22,12],![14,16,38,28]⟩
def cycle736_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle736_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data736 : PartitionData E W := ⟨6,![cycle736_0,cycle736_1,cycle736_2,cycle736_3,cycle736_4,cycle736_5]⟩
lemma valid_data736 : data736.Valid src736 dst736 Finset.univ := by decide +kernel

def src737 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst737 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle737_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle737_1 : CycleData E W := ⟨3,![3,15,18,8,7],![3,4,26,16,18]⟩
def cycle737_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle737_3 : CycleData E W := ⟨2,![9,19,24,12],![14,16,39,28]⟩
def cycle737_4 : CycleData E W := ⟨3,![13,23,22,17,14],![5,28,18,38,26]⟩
def cycle737_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data737 : PartitionData E W := ⟨6,![cycle737_0,cycle737_1,cycle737_2,cycle737_3,cycle737_4,cycle737_5]⟩
lemma valid_data737 : data737.Valid src737 dst737 Finset.univ := by decide +kernel

def src738 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,38,16,26,39,8,38,28,18,39]
def dst738 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,38,16,26,39,6,38,28,18,39,8]
def cycle738_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle738_1 : CycleData E W := ⟨2,![3,15,23,7],![3,4,28,18]⟩
def cycle738_2 : CycleData E W := ⟨3,![5,4,11,12,10],![2,8,4,26,14]⟩
def cycle738_3 : CycleData E W := ⟨2,![8,24,19,18],![16,18,39,26]⟩
def cycle738_4 : CycleData E W := ⟨3,![13,9,17,22,14],![5,14,16,38,28]⟩
def cycle738_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data738 : PartitionData E W := ⟨6,![cycle738_0,cycle738_1,cycle738_2,cycle738_3,cycle738_4,cycle738_5]⟩
lemma valid_data738 : data738.Valid src738 dst738 Finset.univ := by decide +kernel

def src739 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,38,26,16,39,8,38,18,28,39]
def dst739 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,38,26,16,39,6,38,18,28,39,8]
def cycle739_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle739_1 : CycleData E W := ⟨3,![3,11,17,22,7],![3,4,26,38,18]⟩
def cycle739_2 : CycleData E W := ⟨4,![5,4,15,14,13,10],![2,8,4,28,5,14]⟩
def cycle739_3 : CycleData E W := ⟨2,![8,23,24,19],![16,18,28,39]⟩
def cycle739_4 : CycleData E W := ⟨1,![9,18,12],![14,16,26]⟩
def cycle739_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data739 : PartitionData E W := ⟨6,![cycle739_0,cycle739_1,cycle739_2,cycle739_3,cycle739_4,cycle739_5]⟩
lemma valid_data739 : data739.Valid src739 dst739 Finset.univ := by decide +kernel

def src740 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,38,26,39,8,38,18,28,39]
def dst740 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,38,26,39,6,38,18,28,39,8]
def cycle740_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle740_1 : CycleData E W := ⟨2,![1,20,19,14],![5,6,39,26]⟩
def cycle740_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle740_3 : CycleData E W := ⟨2,![4,21,18,15],![4,8,38,26]⟩
def cycle740_4 : CycleData E W := ⟨3,![5,25,24,23,10],![2,8,39,28,18]⟩
def cycle740_5 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def data740 : PartitionData E W := ⟨6,![cycle740_0,cycle740_1,cycle740_2,cycle740_3,cycle740_4,cycle740_5]⟩
lemma valid_data740 : data740.Valid src740 dst740 Finset.univ := by decide +kernel

def src741 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,38,26,39,8,38,28,18,39]
def dst741 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,38,26,39,6,38,28,18,39,8]
def cycle741_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle741_1 : CycleData E W := ⟨2,![1,20,19,14],![5,6,39,26]⟩
def cycle741_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle741_3 : CycleData E W := ⟨2,![4,21,18,15],![4,8,38,26]⟩
def cycle741_4 : CycleData E W := ⟨2,![5,25,24,10],![2,8,39,18]⟩
def cycle741_5 : CycleData E W := ⟨3,![8,17,22,23,9],![3,16,38,28,18]⟩
def data741 : PartitionData E W := ⟨6,![cycle741_0,cycle741_1,cycle741_2,cycle741_3,cycle741_4,cycle741_5]⟩
lemma valid_data741 : data741.Valid src741 dst741 Finset.univ := by decide +kernel

def src742 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,39,26,38,8,38,18,28,39]
def dst742 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,39,26,38,6,38,18,28,39,8]
def cycle742_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle742_1 : CycleData E W := ⟨2,![1,20,19,14],![5,6,38,26]⟩
def cycle742_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle742_3 : CycleData E W := ⟨2,![4,25,18,15],![4,8,39,26]⟩
def cycle742_4 : CycleData E W := ⟨2,![5,21,22,10],![2,8,38,18]⟩
def cycle742_5 : CycleData E W := ⟨3,![8,17,24,23,9],![3,16,39,28,18]⟩
def data742 : PartitionData E W := ⟨6,![cycle742_0,cycle742_1,cycle742_2,cycle742_3,cycle742_4,cycle742_5]⟩
lemma valid_data742 : data742.Valid src742 dst742 Finset.univ := by decide +kernel

def src743 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,39,26,38,8,38,28,18,39]
def dst743 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,39,26,38,6,38,28,18,39,8]
def cycle743_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle743_1 : CycleData E W := ⟨2,![1,20,19,14],![5,6,38,26]⟩
def cycle743_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle743_3 : CycleData E W := ⟨2,![4,25,18,15],![4,8,39,26]⟩
def cycle743_4 : CycleData E W := ⟨3,![5,21,22,23,10],![2,8,38,28,18]⟩
def cycle743_5 : CycleData E W := ⟨2,![8,17,24,9],![3,16,39,18]⟩
def data743 : PartitionData E W := ⟨6,![cycle743_0,cycle743_1,cycle743_2,cycle743_3,cycle743_4,cycle743_5]⟩
lemma valid_data743 : data743.Valid src743 dst743 Finset.univ := by decide +kernel

def src744 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,18,38,28,39]
def dst744 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,18,38,28,39,8]
def cycle744_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,5,3,18]⟩
def cycle744_1 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle744_2 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle744_3 : CycleData E W := ⟨2,![7,17,23,12],![14,16,38,28]⟩
def cycle744_4 : CycleData E W := ⟨2,![13,24,19,14],![5,28,39,26]⟩
def cycle744_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data744 : PartitionData E W := ⟨6,![cycle744_0,cycle744_1,cycle744_2,cycle744_3,cycle744_4,cycle744_5]⟩
lemma valid_data744 : data744.Valid src744 dst744 Finset.univ := by decide +kernel

def src745 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,18,39,28,38]
def dst745 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,18,39,28,38,8]
def cycle745_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,5,3,18]⟩
def cycle745_1 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle745_2 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle745_3 : CycleData E W := ⟨2,![7,17,24,12],![14,16,38,28]⟩
def cycle745_4 : CycleData E W := ⟨2,![13,23,19,14],![5,28,39,26]⟩
def cycle745_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data745 : PartitionData E W := ⟨6,![cycle745_0,cycle745_1,cycle745_2,cycle745_3,cycle745_4,cycle745_5]⟩
lemma valid_data745 : data745.Valid src745 dst745 Finset.univ := by decide +kernel

def src746 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,38,16,26,39,8,38,28,18,39]
def dst746 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,38,16,26,39,6,38,28,18,39,8]
def cycle746_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,5,3,18]⟩
def cycle746_1 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle746_2 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle746_3 : CycleData E W := ⟨2,![7,17,22,12],![14,16,38,28]⟩
def cycle746_4 : CycleData E W := ⟨3,![13,23,24,19,14],![5,28,18,39,26]⟩
def cycle746_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data746 : PartitionData E W := ⟨6,![cycle746_0,cycle746_1,cycle746_2,cycle746_3,cycle746_4,cycle746_5]⟩
lemma valid_data746 : data746.Valid src746 dst746 Finset.univ := by decide +kernel

def src747 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,18,38,28,39]
def dst747 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,18,38,28,39,8]
def cycle747_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,5,3,18]⟩
def cycle747_1 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle747_2 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle747_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle747_4 : CycleData E W := ⟨2,![13,23,17,14],![5,28,38,26]⟩
def cycle747_5 : CycleData E W := ⟨3,![16,22,21,25,20],![6,38,18,8,39]⟩
def data747 : PartitionData E W := ⟨6,![cycle747_0,cycle747_1,cycle747_2,cycle747_3,cycle747_4,cycle747_5]⟩
lemma valid_data747 : data747.Valid src747 dst747 Finset.univ := by decide +kernel

def src748 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,18,39,28,38]
def dst748 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,18,39,28,38,8]
def cycle748_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,5,3,18]⟩
def cycle748_1 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle748_2 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle748_3 : CycleData E W := ⟨2,![7,19,23,12],![14,16,39,28]⟩
def cycle748_4 : CycleData E W := ⟨2,![13,24,17,14],![5,28,38,26]⟩
def cycle748_5 : CycleData E W := ⟨3,![16,25,21,22,20],![6,38,8,18,39]⟩
def data748 : PartitionData E W := ⟨6,![cycle748_0,cycle748_1,cycle748_2,cycle748_3,cycle748_4,cycle748_5]⟩
lemma valid_data748 : data748.Valid src748 dst748 Finset.univ := by decide +kernel

def src749 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,38,26,16,39,8,38,18,28,39]
def dst749 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,38,26,16,39,6,38,18,28,39,8]
def cycle749_0 : CycleData E W := ⟨3,![0,1,2,9,10],![2,6,5,3,18]⟩
def cycle749_1 : CycleData E W := ⟨2,![3,15,18,8],![3,4,26,16]⟩
def cycle749_2 : CycleData E W := ⟨2,![5,4,11,6],![2,8,4,14]⟩
def cycle749_3 : CycleData E W := ⟨2,![7,19,24,12],![14,16,39,28]⟩
def cycle749_4 : CycleData E W := ⟨3,![13,23,22,17,14],![5,28,18,38,26]⟩
def cycle749_5 : CycleData E W := ⟨2,![16,21,25,20],![6,38,8,39]⟩
def data749 : PartitionData E W := ⟨6,![cycle749_0,cycle749_1,cycle749_2,cycle749_3,cycle749_4,cycle749_5]⟩
lemma valid_data749 : data749.Valid src749 dst749 Finset.univ := by decide +kernel

def lookupB14 (j : ℕ) : PartitionData E W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data700 else (if j < 2 then data701 else data702)) else (if j < 4 then data703 else (if j < 5 then data704 else data705))) else (if j < 9 then (if j < 7 then data706 else (if j < 8 then data707 else data708)) else (if j < 10 then data709 else (if j < 11 then data710 else data711)))) else (if j < 18 then (if j < 15 then (if j < 13 then data712 else (if j < 14 then data713 else data714)) else (if j < 16 then data715 else (if j < 17 then data716 else data717))) else (if j < 21 then (if j < 19 then data718 else (if j < 20 then data719 else data720)) else (if j < 23 then (if j < 22 then data721 else data722) else (if j < 24 then data723 else data724))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data725 else (if j < 27 then data726 else data727)) else (if j < 29 then data728 else (if j < 30 then data729 else data730))) else (if j < 34 then (if j < 32 then data731 else (if j < 33 then data732 else data733)) else (if j < 35 then data734 else (if j < 36 then data735 else data736)))) else (if j < 43 then (if j < 40 then (if j < 38 then data737 else (if j < 39 then data738 else data739)) else (if j < 41 then data740 else (if j < 42 then data741 else data742))) else (if j < 46 then (if j < 44 then data743 else (if j < 45 then data744 else data745)) else (if j < 48 then (if j < 47 then data746 else data747) else (if j < 49 then data748 else data749))))))

def srcTableB14 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src700 else (if j < 2 then src701 else src702)) else (if j < 4 then src703 else (if j < 5 then src704 else src705))) else (if j < 9 then (if j < 7 then src706 else (if j < 8 then src707 else src708)) else (if j < 10 then src709 else (if j < 11 then src710 else src711)))) else (if j < 18 then (if j < 15 then (if j < 13 then src712 else (if j < 14 then src713 else src714)) else (if j < 16 then src715 else (if j < 17 then src716 else src717))) else (if j < 21 then (if j < 19 then src718 else (if j < 20 then src719 else src720)) else (if j < 23 then (if j < 22 then src721 else src722) else (if j < 24 then src723 else src724))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src725 else (if j < 27 then src726 else src727)) else (if j < 29 then src728 else (if j < 30 then src729 else src730))) else (if j < 34 then (if j < 32 then src731 else (if j < 33 then src732 else src733)) else (if j < 35 then src734 else (if j < 36 then src735 else src736)))) else (if j < 43 then (if j < 40 then (if j < 38 then src737 else (if j < 39 then src738 else src739)) else (if j < 41 then src740 else (if j < 42 then src741 else src742))) else (if j < 46 then (if j < 44 then src743 else (if j < 45 then src744 else src745)) else (if j < 48 then (if j < 47 then src746 else src747) else (if j < 49 then src748 else src749))))))

def dstTableB14 (j : ℕ) : E → W := (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst700 else (if j < 2 then dst701 else dst702)) else (if j < 4 then dst703 else (if j < 5 then dst704 else dst705))) else (if j < 9 then (if j < 7 then dst706 else (if j < 8 then dst707 else dst708)) else (if j < 10 then dst709 else (if j < 11 then dst710 else dst711)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst712 else (if j < 14 then dst713 else dst714)) else (if j < 16 then dst715 else (if j < 17 then dst716 else dst717))) else (if j < 21 then (if j < 19 then dst718 else (if j < 20 then dst719 else dst720)) else (if j < 23 then (if j < 22 then dst721 else dst722) else (if j < 24 then dst723 else dst724))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst725 else (if j < 27 then dst726 else dst727)) else (if j < 29 then dst728 else (if j < 30 then dst729 else dst730))) else (if j < 34 then (if j < 32 then dst731 else (if j < 33 then dst732 else dst733)) else (if j < 35 then dst734 else (if j < 36 then dst735 else dst736)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst737 else (if j < 39 then dst738 else dst739)) else (if j < 41 then dst740 else (if j < 42 then dst741 else dst742))) else (if j < 46 then (if j < 44 then dst743 else (if j < 45 then dst744 else dst745)) else (if j < 48 then (if j < 47 then dst746 else dst747) else (if j < 49 then dst748 else dst749))))))

def caseB14 (i : Fin 50) : Cases := ⟨700 + i.val,by have := i.isLt; omega⟩
lemma tableB14_valid (i : Fin 50) :
    (lookupB14 i.val).Valid (srcTableB14 i.val) (dstTableB14 i.val) Finset.univ := by
  fin_cases i
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

lemma srcB14_row : ∀ (i : Fin 50) (e : E),
    srcTableB14 i.val e = caseSource (caseB14 i) e := by decide +kernel

lemma dstB14_row : ∀ (i : Fin 50) (e : E),
    dstTableB14 i.val e = caseTarget (caseB14 i) e := by decide +kernel

lemma sizeB14 : ∀ i : Fin 50, (lookupB14 i.val).size ≤ 5 →
    (lookupB14 i.val).size = 2 ∧
      (⟨caseKey (caseB14 i),caseKey_lt (caseB14 i)⟩ : Fin 1244160) ∈ good := by decide +kernel
lemma certificateB14 (i : Fin 50) : Certificate (caseB14 i) := by
  refine ⟨lookupB14 i.val,?_,sizeB14 i⟩
  have hv := tableB14_valid i
  rw [funext (srcB14_row i),funext (dstB14_row i)] at hv
  exact hv
lemma certificateInterval14 : FiniteIntervals.Covers CertificateAt 700 750 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 700 50 (fun i _ => certificateB14 i)
#print axioms certificateInterval14
end Erdos184Work.FiveRows4

import Submission.FiveCertificates1Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows1
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src800 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst800 : E → W := ![4,3,6,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle800_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle800_1 : CycleData E W := ⟨2,![1,13,14,2],![3,4,26,6]⟩
def cycle800_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle800_3 : CycleData E W := ⟨3,![4,18,12,15,9],![2,8,28,26,16]⟩
def cycle800_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle800_5 : CycleData E W := ⟨2,![7,20,16,8],![3,18,38,16]⟩
def data800 : PartitionData E W := ⟨6,![cycle800_0,cycle800_1,cycle800_2,cycle800_3,cycle800_4,cycle800_5]⟩
lemma valid_data800 : data800.Valid src800 dst800 Finset.univ := by decide +kernel

def src801 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst801 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle801_0 : CycleData E W := ⟨2,![0,10,15,9],![2,4,26,16]⟩
def cycle801_1 : CycleData E W := ⟨2,![1,13,19,7],![3,4,28,18]⟩
def cycle801_2 : CycleData E W := ⟨1,![2,14,8],![3,6,16]⟩
def cycle801_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle801_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle801_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data801 : PartitionData E W := ⟨6,![cycle801_0,cycle801_1,cycle801_2,cycle801_3,cycle801_4,cycle801_5]⟩
lemma valid_data801 : data801.Valid src801 dst801 Finset.univ := by decide +kernel

def src802 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst802 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle802_0 : CycleData E W := ⟨9,![4,18,6,12,13,10,16,17,2,8,9],![2,8,18,14,28,4,26,38,6,3,16]⟩
def cycle802_1 : CycleData E W := ⟨9,![0,1,7,19,20,21,3,14,15,11,5],![2,4,3,18,38,28,8,6,16,26,14]⟩
def data802 : PartitionData E W := ⟨2,![cycle802_0,cycle802_1]⟩
lemma valid_data802 : data802.Valid src802 dst802 Finset.univ := by decide +kernel

def src803 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst803 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle803_0 : CycleData E W := ⟨2,![0,10,15,9],![2,4,26,16]⟩
def cycle803_1 : CycleData E W := ⟨2,![1,13,19,7],![3,4,28,18]⟩
def cycle803_2 : CycleData E W := ⟨1,![2,14,8],![3,6,16]⟩
def cycle803_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle803_4 : CycleData E W := ⟨2,![4,18,12,5],![2,8,28,14]⟩
def cycle803_5 : CycleData E W := ⟨2,![6,20,16,11],![14,18,38,26]⟩
def data803 : PartitionData E W := ⟨6,![cycle803_0,cycle803_1,cycle803_2,cycle803_3,cycle803_4,cycle803_5]⟩
lemma valid_data803 : data803.Valid src803 dst803 Finset.univ := by decide +kernel

def src804 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst804 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle804_0 : CycleData E W := ⟨9,![0,13,12,11,16,15,14,2,7,18,4],![2,4,28,14,26,38,16,6,3,18,8]⟩
def cycle804_1 : CycleData E W := ⟨9,![5,6,19,20,21,3,17,10,1,8,9],![2,14,18,28,38,8,6,26,4,3,16]⟩
def data804 : PartitionData E W := ⟨2,![cycle804_0,cycle804_1]⟩
lemma valid_data804 : data804.Valid src804 dst804 Finset.univ := by decide +kernel

def src805 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst805 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle805_0 : CycleData E W := ⟨9,![0,13,12,11,16,15,14,2,7,18,4],![2,4,28,14,26,38,16,6,3,18,8]⟩
def cycle805_1 : CycleData E W := ⟨9,![5,6,19,20,21,3,17,10,1,8,9],![2,14,18,38,28,8,6,26,4,3,16]⟩
def data805 : PartitionData E W := ⟨2,![cycle805_0,cycle805_1]⟩
lemma valid_data805 : data805.Valid src805 dst805 Finset.univ := by decide +kernel

def src806 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst806 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle806_0 : CycleData E W := ⟨9,![5,6,7,2,3,18,13,10,16,15,9],![2,14,18,3,6,8,28,4,26,38,16]⟩
def cycle806_1 : CycleData E W := ⟨9,![0,1,8,14,17,11,12,19,20,21,4],![2,4,3,16,6,26,14,28,18,38,8]⟩
def data806 : PartitionData E W := ⟨2,![cycle806_0,cycle806_1]⟩
lemma valid_data806 : data806.Valid src806 dst806 Finset.univ := by decide +kernel

def src807 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst807 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle807_0 : CycleData E W := ⟨9,![4,18,7,8,16,17,14,10,13,12,5],![2,8,18,3,16,38,6,26,4,28,14]⟩
def cycle807_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,6,11,15,9],![2,4,3,6,8,38,28,18,14,26,16]⟩
def data807 : PartitionData E W := ⟨2,![cycle807_0,cycle807_1]⟩
lemma valid_data807 : data807.Valid src807 dst807 Finset.univ := by decide +kernel

def src808 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst808 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle808_0 : CycleData E W := ⟨9,![4,18,7,8,16,17,14,10,13,12,5],![2,8,18,3,16,38,6,26,4,28,14]⟩
def cycle808_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,6,11,15,9],![2,4,3,6,8,28,38,18,14,26,16]⟩
def data808 : PartitionData E W := ⟨2,![cycle808_0,cycle808_1]⟩
lemma valid_data808 : data808.Valid src808 dst808 Finset.univ := by decide +kernel

def src809 : E → W := ![2,4,3,6,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst809 : E → W := ![4,3,6,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle809_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle809_1 : CycleData E W := ⟨2,![1,10,14,2],![3,4,26,6]⟩
def cycle809_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle809_3 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle809_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle809_5 : CycleData E W := ⟨2,![7,20,16,8],![3,18,38,16]⟩
def data809 : PartitionData E W := ⟨6,![cycle809_0,cycle809_1,cycle809_2,cycle809_3,cycle809_4,cycle809_5]⟩
lemma valid_data809 : data809.Valid src809 dst809 Finset.univ := by decide +kernel

def src810 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst810 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle810_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle810_1 : CycleData E W := ⟨3,![2,14,15,11,7],![3,6,16,26,14]⟩
def cycle810_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle810_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle810_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle810_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data810 : PartitionData E W := ⟨6,![cycle810_0,cycle810_1,cycle810_2,cycle810_3,cycle810_4,cycle810_5]⟩
lemma valid_data810 : data810.Valid src810 dst810 Finset.univ := by decide +kernel

def src811 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst811 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle811_0 : CycleData E W := ⟨3,![0,13,12,15,5],![2,4,28,26,16]⟩
def cycle811_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle811_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle811_3 : CycleData E W := ⟨2,![3,21,20,17],![6,8,28,38]⟩
def cycle811_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle811_5 : CycleData E W := ⟨2,![8,19,16,11],![14,18,38,26]⟩
def data811 : PartitionData E W := ⟨6,![cycle811_0,cycle811_1,cycle811_2,cycle811_3,cycle811_4,cycle811_5]⟩
lemma valid_data811 : data811.Valid src811 dst811 Finset.univ := by decide +kernel

def src812 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst812 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle812_0 : CycleData E W := ⟨3,![0,13,12,15,5],![2,4,28,26,16]⟩
def cycle812_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle812_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle812_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle812_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle812_5 : CycleData E W := ⟨2,![8,20,16,11],![14,18,38,26]⟩
def data812 : PartitionData E W := ⟨6,![cycle812_0,cycle812_1,cycle812_2,cycle812_3,cycle812_4,cycle812_5]⟩
lemma valid_data812 : data812.Valid src812 dst812 Finset.univ := by decide +kernel

def src813 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst813 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle813_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle813_1 : CycleData E W := ⟨2,![2,17,11,7],![3,6,26,14]⟩
def cycle813_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle813_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle813_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle813_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data813 : PartitionData E W := ⟨6,![cycle813_0,cycle813_1,cycle813_2,cycle813_3,cycle813_4,cycle813_5]⟩
lemma valid_data813 : data813.Valid src813 dst813 Finset.univ := by decide +kernel

def src814 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst814 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle814_0 : CycleData E W := ⟨3,![0,13,20,15,5],![2,4,28,38,16]⟩
def cycle814_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle814_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle814_3 : CycleData E W := ⟨2,![3,21,12,17],![6,8,28,26]⟩
def cycle814_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle814_5 : CycleData E W := ⟨2,![8,19,16,11],![14,18,38,26]⟩
def data814 : PartitionData E W := ⟨6,![cycle814_0,cycle814_1,cycle814_2,cycle814_3,cycle814_4,cycle814_5]⟩
lemma valid_data814 : data814.Valid src814 dst814 Finset.univ := by decide +kernel

def src815 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst815 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle815_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle815_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle815_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle815_3 : CycleData E W := ⟨2,![3,21,16,17],![6,8,38,26]⟩
def cycle815_4 : CycleData E W := ⟨2,![5,15,20,9],![2,16,38,18]⟩
def cycle815_5 : CycleData E W := ⟨2,![8,19,12,11],![14,18,28,26]⟩
def data815 : PartitionData E W := ⟨6,![cycle815_0,cycle815_1,cycle815_2,cycle815_3,cycle815_4,cycle815_5]⟩
lemma valid_data815 : data815.Valid src815 dst815 Finset.univ := by decide +kernel

def src816 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst816 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle816_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle816_1 : CycleData E W := ⟨2,![2,14,11,7],![3,6,26,14]⟩
def cycle816_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle816_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle816_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle816_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data816 : PartitionData E W := ⟨6,![cycle816_0,cycle816_1,cycle816_2,cycle816_3,cycle816_4,cycle816_5]⟩
lemma valid_data816 : data816.Valid src816 dst816 Finset.univ := by decide +kernel

def src817 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst817 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle817_0 : CycleData E W := ⟨9,![4,18,8,11,12,13,1,2,17,16,5],![2,8,18,14,26,28,4,3,6,38,16]⟩
def cycle817_1 : CycleData E W := ⟨9,![0,10,7,6,15,14,3,21,20,19,9],![2,4,14,3,16,26,6,8,28,38,18]⟩
def data817 : PartitionData E W := ⟨2,![cycle817_0,cycle817_1]⟩
lemma valid_data817 : data817.Valid src817 dst817 Finset.univ := by decide +kernel

def src818 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst818 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle818_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle818_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle818_2 : CycleData E W := ⟨2,![2,14,15,6],![3,6,26,16]⟩
def cycle818_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle818_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle818_5 : CycleData E W := ⟨2,![8,19,12,11],![14,18,28,26]⟩
def data818 : PartitionData E W := ⟨6,![cycle818_0,cycle818_1,cycle818_2,cycle818_3,cycle818_4,cycle818_5]⟩
lemma valid_data818 : data818.Valid src818 dst818 Finset.univ := by decide +kernel

def src819 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst819 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle819_0 : CycleData E W := ⟨2,![0,13,15,5],![2,4,26,16]⟩
def cycle819_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle819_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle819_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle819_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle819_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle819_6 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data819 : PartitionData E W := ⟨7,![cycle819_0,cycle819_1,cycle819_2,cycle819_3,cycle819_4,cycle819_5,cycle819_6]⟩
lemma valid_data819 : data819.Valid src819 dst819 Finset.univ := by decide +kernel

def src820 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst820 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle820_0 : CycleData E W := ⟨2,![0,13,15,5],![2,4,26,16]⟩
def cycle820_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle820_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle820_3 : CycleData E W := ⟨3,![4,3,17,19,9],![2,8,6,38,18]⟩
def cycle820_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle820_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data820 : PartitionData E W := ⟨6,![cycle820_0,cycle820_1,cycle820_2,cycle820_3,cycle820_4,cycle820_5]⟩
lemma valid_data820 : data820.Valid src820 dst820 Finset.univ := by decide +kernel

def src821 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst821 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle821_0 : CycleData E W := ⟨2,![0,13,15,5],![2,4,26,16]⟩
def cycle821_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle821_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle821_3 : CycleData E W := ⟨3,![3,18,12,16,17],![6,8,28,26,38]⟩
def cycle821_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle821_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data821 : PartitionData E W := ⟨6,![cycle821_0,cycle821_1,cycle821_2,cycle821_3,cycle821_4,cycle821_5]⟩
lemma valid_data821 : data821.Valid src821 dst821 Finset.univ := by decide +kernel

def src822 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst822 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle822_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle822_1 : CycleData E W := ⟨3,![2,17,13,10,7],![3,6,26,4,14]⟩
def cycle822_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle822_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle822_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle822_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data822 : PartitionData E W := ⟨6,![cycle822_0,cycle822_1,cycle822_2,cycle822_3,cycle822_4,cycle822_5]⟩
lemma valid_data822 : data822.Valid src822 dst822 Finset.univ := by decide +kernel

def src823 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst823 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle823_0 : CycleData E W := ⟨3,![0,13,16,15,5],![2,4,26,38,16]⟩
def cycle823_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle823_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle823_3 : CycleData E W := ⟨2,![3,21,12,17],![6,8,28,26]⟩
def cycle823_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle823_5 : CycleData E W := ⟨2,![8,19,20,11],![14,18,38,28]⟩
def data823 : PartitionData E W := ⟨6,![cycle823_0,cycle823_1,cycle823_2,cycle823_3,cycle823_4,cycle823_5]⟩
lemma valid_data823 : data823.Valid src823 dst823 Finset.univ := by decide +kernel

def src824 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst824 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle824_0 : CycleData E W := ⟨3,![0,13,16,15,5],![2,4,26,38,16]⟩
def cycle824_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle824_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle824_3 : CycleData E W := ⟨2,![3,18,12,17],![6,8,28,26]⟩
def cycle824_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle824_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data824 : PartitionData E W := ⟨6,![cycle824_0,cycle824_1,cycle824_2,cycle824_3,cycle824_4,cycle824_5]⟩
lemma valid_data824 : data824.Valid src824 dst824 Finset.univ := by decide +kernel

def src825 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst825 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle825_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle825_1 : CycleData E W := ⟨3,![2,14,13,10,7],![3,6,26,4,14]⟩
def cycle825_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle825_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle825_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle825_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data825 : PartitionData E W := ⟨6,![cycle825_0,cycle825_1,cycle825_2,cycle825_3,cycle825_4,cycle825_5]⟩
lemma valid_data825 : data825.Valid src825 dst825 Finset.univ := by decide +kernel

def src826 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst826 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle826_0 : CycleData E W := ⟨2,![0,13,15,5],![2,4,26,16]⟩
def cycle826_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle826_2 : CycleData E W := ⟨2,![2,17,16,6],![3,6,38,16]⟩
def cycle826_3 : CycleData E W := ⟨2,![3,21,12,14],![6,8,28,26]⟩
def cycle826_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle826_5 : CycleData E W := ⟨2,![8,19,20,11],![14,18,38,28]⟩
def data826 : PartitionData E W := ⟨6,![cycle826_0,cycle826_1,cycle826_2,cycle826_3,cycle826_4,cycle826_5]⟩
lemma valid_data826 : data826.Valid src826 dst826 Finset.univ := by decide +kernel

def src827 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst827 : E → W := ![4,3,6,8,2,16,3,14,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle827_0 : CycleData E W := ⟨2,![0,13,15,5],![2,4,26,16]⟩
def cycle827_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle827_2 : CycleData E W := ⟨2,![2,17,16,6],![3,6,38,16]⟩
def cycle827_3 : CycleData E W := ⟨2,![3,18,12,14],![6,8,28,26]⟩
def cycle827_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle827_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data827 : PartitionData E W := ⟨6,![cycle827_0,cycle827_1,cycle827_2,cycle827_3,cycle827_4,cycle827_5]⟩
lemma valid_data827 : data827.Valid src827 dst827 Finset.univ := by decide +kernel

def src828 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst828 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle828_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle828_1 : CycleData E W := ⟨3,![2,14,15,11,7],![3,6,16,26,14]⟩
def cycle828_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle828_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle828_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle828_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data828 : PartitionData E W := ⟨6,![cycle828_0,cycle828_1,cycle828_2,cycle828_3,cycle828_4,cycle828_5]⟩
lemma valid_data828 : data828.Valid src828 dst828 Finset.univ := by decide +kernel

def src829 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst829 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle829_0 : CycleData E W := ⟨2,![0,10,15,5],![2,4,26,16]⟩
def cycle829_1 : CycleData E W := ⟨2,![1,13,12,7],![3,4,28,14]⟩
def cycle829_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle829_3 : CycleData E W := ⟨2,![3,21,20,17],![6,8,28,38]⟩
def cycle829_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle829_5 : CycleData E W := ⟨2,![8,19,16,11],![14,18,38,26]⟩
def data829 : PartitionData E W := ⟨6,![cycle829_0,cycle829_1,cycle829_2,cycle829_3,cycle829_4,cycle829_5]⟩
lemma valid_data829 : data829.Valid src829 dst829 Finset.univ := by decide +kernel

def src830 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst830 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle830_0 : CycleData E W := ⟨2,![0,10,15,5],![2,4,26,16]⟩
def cycle830_1 : CycleData E W := ⟨2,![1,13,12,7],![3,4,28,14]⟩
def cycle830_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle830_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle830_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle830_5 : CycleData E W := ⟨2,![8,20,16,11],![14,18,38,26]⟩
def data830 : PartitionData E W := ⟨6,![cycle830_0,cycle830_1,cycle830_2,cycle830_3,cycle830_4,cycle830_5]⟩
lemma valid_data830 : data830.Valid src830 dst830 Finset.univ := by decide +kernel

def src831 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst831 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle831_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle831_1 : CycleData E W := ⟨2,![2,17,11,7],![3,6,26,14]⟩
def cycle831_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle831_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle831_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle831_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data831 : PartitionData E W := ⟨6,![cycle831_0,cycle831_1,cycle831_2,cycle831_3,cycle831_4,cycle831_5]⟩
lemma valid_data831 : data831.Valid src831 dst831 Finset.univ := by decide +kernel

def src832 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst832 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle832_0 : CycleData E W := ⟨9,![5,15,16,10,13,12,7,2,3,18,9],![2,16,38,26,4,28,14,3,6,8,18]⟩
def cycle832_1 : CycleData E W := ⟨9,![0,1,6,14,17,11,8,19,20,21,4],![2,4,3,16,6,26,14,18,38,28,8]⟩
def data832 : PartitionData E W := ⟨2,![cycle832_0,cycle832_1]⟩
lemma valid_data832 : data832.Valid src832 dst832 Finset.univ := by decide +kernel

def src833 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst833 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle833_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle833_1 : CycleData E W := ⟨2,![1,10,11,7],![3,4,26,14]⟩
def cycle833_2 : CycleData E W := ⟨1,![2,14,6],![3,6,16]⟩
def cycle833_3 : CycleData E W := ⟨2,![3,21,16,17],![6,8,38,26]⟩
def cycle833_4 : CycleData E W := ⟨2,![5,15,20,9],![2,16,38,18]⟩
def cycle833_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data833 : PartitionData E W := ⟨6,![cycle833_0,cycle833_1,cycle833_2,cycle833_3,cycle833_4,cycle833_5]⟩
lemma valid_data833 : data833.Valid src833 dst833 Finset.univ := by decide +kernel

def src834 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst834 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle834_0 : CycleData E W := ⟨2,![0,1,6,5],![2,4,3,16]⟩
def cycle834_1 : CycleData E W := ⟨2,![2,14,11,7],![3,6,26,14]⟩
def cycle834_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle834_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle834_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle834_5 : CycleData E W := ⟨3,![10,15,16,20,13],![4,26,16,38,28]⟩
def data834 : PartitionData E W := ⟨6,![cycle834_0,cycle834_1,cycle834_2,cycle834_3,cycle834_4,cycle834_5]⟩
lemma valid_data834 : data834.Valid src834 dst834 Finset.univ := by decide +kernel

def src835 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst835 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle835_0 : CycleData E W := ⟨9,![4,3,14,10,13,12,7,6,16,19,9],![2,8,6,26,4,28,14,3,16,38,18]⟩
def cycle835_1 : CycleData E W := ⟨9,![0,1,2,17,20,21,18,8,11,15,5],![2,4,3,6,38,28,8,18,14,26,16]⟩
def data835 : PartitionData E W := ⟨2,![cycle835_0,cycle835_1]⟩
lemma valid_data835 : data835.Valid src835 dst835 Finset.univ := by decide +kernel

def src836 : E → W := ![2,4,3,6,8,2,16,3,14,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst836 : E → W := ![4,3,6,8,2,16,3,14,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle836_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle836_1 : CycleData E W := ⟨2,![1,10,11,7],![3,4,26,14]⟩
def cycle836_2 : CycleData E W := ⟨2,![2,14,15,6],![3,6,26,16]⟩
def cycle836_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle836_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle836_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data836 : PartitionData E W := ⟨6,![cycle836_0,cycle836_1,cycle836_2,cycle836_3,cycle836_4,cycle836_5]⟩
lemma valid_data836 : data836.Valid src836 dst836 Finset.univ := by decide +kernel

def src837 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst837 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle837_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,16]⟩
def cycle837_1 : CycleData E W := ⟨2,![1,13,19,8],![3,4,28,18]⟩
def cycle837_2 : CycleData E W := ⟨3,![2,14,15,11,7],![3,6,16,26,14]⟩
def cycle837_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle837_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle837_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data837 : PartitionData E W := ⟨6,![cycle837_0,cycle837_1,cycle837_2,cycle837_3,cycle837_4,cycle837_5]⟩
lemma valid_data837 : data837.Valid src837 dst837 Finset.univ := by decide +kernel

def src838 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst838 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle838_0 : CycleData E W := ⟨2,![0,13,21,4],![2,4,28,8]⟩
def cycle838_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle838_2 : CycleData E W := ⟨3,![5,14,2,8,9],![2,16,6,3,18]⟩
def cycle838_3 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle838_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle838_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data838 : PartitionData E W := ⟨6,![cycle838_0,cycle838_1,cycle838_2,cycle838_3,cycle838_4,cycle838_5]⟩
lemma valid_data838 : data838.Valid src838 dst838 Finset.univ := by decide +kernel

def src839 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst839 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle839_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle839_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle839_2 : CycleData E W := ⟨3,![5,14,2,8,9],![2,16,6,3,18]⟩
def cycle839_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle839_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle839_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data839 : PartitionData E W := ⟨6,![cycle839_0,cycle839_1,cycle839_2,cycle839_3,cycle839_4,cycle839_5]⟩
lemma valid_data839 : data839.Valid src839 dst839 Finset.univ := by decide +kernel

def src840 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst840 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle840_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,16]⟩
def cycle840_1 : CycleData E W := ⟨2,![1,13,19,8],![3,4,28,18]⟩
def cycle840_2 : CycleData E W := ⟨2,![2,17,11,7],![3,6,26,14]⟩
def cycle840_3 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle840_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle840_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data840 : PartitionData E W := ⟨6,![cycle840_0,cycle840_1,cycle840_2,cycle840_3,cycle840_4,cycle840_5]⟩
lemma valid_data840 : data840.Valid src840 dst840 Finset.univ := by decide +kernel

def src841 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst841 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle841_0 : CycleData E W := ⟨2,![0,13,21,4],![2,4,28,8]⟩
def cycle841_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle841_2 : CycleData E W := ⟨2,![2,3,18,8],![3,6,8,18]⟩
def cycle841_3 : CycleData E W := ⟨2,![5,15,19,9],![2,16,38,18]⟩
def cycle841_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle841_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data841 : PartitionData E W := ⟨6,![cycle841_0,cycle841_1,cycle841_2,cycle841_3,cycle841_4,cycle841_5]⟩
lemma valid_data841 : data841.Valid src841 dst841 Finset.univ := by decide +kernel

def src842 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst842 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle842_0 : CycleData E W := ⟨9,![0,10,6,15,16,12,18,3,2,8,9],![2,4,14,16,38,26,28,8,6,3,18]⟩
def cycle842_1 : CycleData E W := ⟨9,![4,21,20,19,13,1,7,11,17,14,5],![2,8,38,18,28,4,3,14,26,6,16]⟩
def data842 : PartitionData E W := ⟨2,![cycle842_0,cycle842_1]⟩
lemma valid_data842 : data842.Valid src842 dst842 Finset.univ := by decide +kernel

def src843 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst843 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle843_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,16]⟩
def cycle843_1 : CycleData E W := ⟨2,![1,13,19,8],![3,4,28,18]⟩
def cycle843_2 : CycleData E W := ⟨2,![2,14,11,7],![3,6,26,14]⟩
def cycle843_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle843_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle843_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data843 : PartitionData E W := ⟨6,![cycle843_0,cycle843_1,cycle843_2,cycle843_3,cycle843_4,cycle843_5]⟩
lemma valid_data843 : data843.Valid src843 dst843 Finset.univ := by decide +kernel

def src844 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst844 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle844_0 : CycleData E W := ⟨3,![0,13,20,16,5],![2,4,28,38,16]⟩
def cycle844_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle844_2 : CycleData E W := ⟨2,![2,17,19,8],![3,6,38,18]⟩
def cycle844_3 : CycleData E W := ⟨2,![3,21,12,14],![6,8,28,26]⟩
def cycle844_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle844_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data844 : PartitionData E W := ⟨6,![cycle844_0,cycle844_1,cycle844_2,cycle844_3,cycle844_4,cycle844_5]⟩
lemma valid_data844 : data844.Valid src844 dst844 Finset.univ := by decide +kernel

def src845 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst845 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle845_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle845_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle845_2 : CycleData E W := ⟨3,![2,14,12,19,8],![3,6,26,28,18]⟩
def cycle845_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle845_4 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle845_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data845 : PartitionData E W := ⟨6,![cycle845_0,cycle845_1,cycle845_2,cycle845_3,cycle845_4,cycle845_5]⟩
lemma valid_data845 : data845.Valid src845 dst845 Finset.univ := by decide +kernel

def src846 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst846 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle846_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,16]⟩
def cycle846_1 : CycleData E W := ⟨3,![1,13,15,14,2],![3,4,26,16,6]⟩
def cycle846_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle846_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle846_4 : CycleData E W := ⟨2,![7,11,19,8],![3,14,28,18]⟩
def cycle846_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data846 : PartitionData E W := ⟨6,![cycle846_0,cycle846_1,cycle846_2,cycle846_3,cycle846_4,cycle846_5]⟩
lemma valid_data846 : data846.Valid src846 dst846 Finset.univ := by decide +kernel

def src847 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst847 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle847_0 : CycleData E W := ⟨2,![0,13,15,5],![2,4,26,16]⟩
def cycle847_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle847_2 : CycleData E W := ⟨2,![2,17,19,8],![3,6,38,18]⟩
def cycle847_3 : CycleData E W := ⟨3,![3,21,11,6,14],![6,8,28,14,16]⟩
def cycle847_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle847_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data847 : PartitionData E W := ⟨6,![cycle847_0,cycle847_1,cycle847_2,cycle847_3,cycle847_4,cycle847_5]⟩
lemma valid_data847 : data847.Valid src847 dst847 Finset.univ := by decide +kernel

def src848 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst848 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle848_0 : CycleData E W := ⟨9,![5,6,11,18,3,17,16,13,1,8,9],![2,16,14,28,8,6,38,26,4,3,18]⟩
def cycle848_1 : CycleData E W := ⟨9,![0,10,7,2,14,15,12,19,20,21,4],![2,4,14,3,6,16,26,28,18,38,8]⟩
def data848 : PartitionData E W := ⟨2,![cycle848_0,cycle848_1]⟩
lemma valid_data848 : data848.Valid src848 dst848 Finset.univ := by decide +kernel

def src849 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst849 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle849_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,16]⟩
def cycle849_1 : CycleData E W := ⟨2,![1,13,17,2],![3,4,26,6]⟩
def cycle849_2 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle849_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle849_4 : CycleData E W := ⟨2,![7,11,19,8],![3,14,28,18]⟩
def cycle849_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data849 : PartitionData E W := ⟨6,![cycle849_0,cycle849_1,cycle849_2,cycle849_3,cycle849_4,cycle849_5]⟩
lemma valid_data849 : data849.Valid src849 dst849 Finset.univ := by decide +kernel

def src850 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst850 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle850_0 : CycleData E W := ⟨9,![5,15,16,12,11,10,1,2,3,18,9],![2,16,38,26,28,14,4,3,6,8,18]⟩
def cycle850_1 : CycleData E W := ⟨9,![0,13,17,14,6,7,8,19,20,21,4],![2,4,26,6,16,14,3,18,38,28,8]⟩
def data850 : PartitionData E W := ⟨2,![cycle850_0,cycle850_1]⟩
lemma valid_data850 : data850.Valid src850 dst850 Finset.univ := by decide +kernel

def src851 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst851 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle851_0 : CycleData E W := ⟨9,![0,10,6,15,16,12,18,3,2,8,9],![2,4,14,16,38,26,28,8,6,3,18]⟩
def cycle851_1 : CycleData E W := ⟨9,![4,21,20,19,11,7,1,13,17,14,5],![2,8,38,18,28,14,3,4,26,6,16]⟩
def data851 : PartitionData E W := ⟨2,![cycle851_0,cycle851_1]⟩
lemma valid_data851 : data851.Valid src851 dst851 Finset.univ := by decide +kernel

def src852 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst852 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle852_0 : CycleData E W := ⟨2,![0,10,6,5],![2,4,14,16]⟩
def cycle852_1 : CycleData E W := ⟨2,![1,13,14,2],![3,4,26,6]⟩
def cycle852_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle852_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle852_4 : CycleData E W := ⟨2,![7,11,19,8],![3,14,28,18]⟩
def cycle852_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data852 : PartitionData E W := ⟨6,![cycle852_0,cycle852_1,cycle852_2,cycle852_3,cycle852_4,cycle852_5]⟩
lemma valid_data852 : data852.Valid src852 dst852 Finset.univ := by decide +kernel

def src853 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst853 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle853_0 : CycleData E W := ⟨2,![0,13,15,5],![2,4,26,16]⟩
def cycle853_1 : CycleData E W := ⟨1,![1,10,7],![3,4,14]⟩
def cycle853_2 : CycleData E W := ⟨2,![2,17,19,8],![3,6,38,18]⟩
def cycle853_3 : CycleData E W := ⟨2,![3,21,12,14],![6,8,28,26]⟩
def cycle853_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle853_5 : CycleData E W := ⟨2,![6,16,20,11],![14,16,38,28]⟩
def data853 : PartitionData E W := ⟨6,![cycle853_0,cycle853_1,cycle853_2,cycle853_3,cycle853_4,cycle853_5]⟩
lemma valid_data853 : data853.Valid src853 dst853 Finset.univ := by decide +kernel

def src854 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst854 : E → W := ![4,3,6,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle854_0 : CycleData E W := ⟨9,![0,13,12,18,3,17,16,6,7,8,9],![2,4,26,28,8,6,38,16,14,3,18]⟩
def cycle854_1 : CycleData E W := ⟨9,![4,21,20,19,11,10,1,2,14,15,5],![2,8,38,18,28,14,4,3,6,26,16]⟩
def data854 : PartitionData E W := ⟨2,![cycle854_0,cycle854_1]⟩
lemma valid_data854 : data854.Valid src854 dst854 Finset.univ := by decide +kernel

def src855 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst855 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle855_0 : CycleData E W := ⟨3,![0,1,2,14,5],![2,4,3,6,16]⟩
def cycle855_1 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle855_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle855_3 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle855_4 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def cycle855_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data855 : PartitionData E W := ⟨6,![cycle855_0,cycle855_1,cycle855_2,cycle855_3,cycle855_4,cycle855_5]⟩
lemma valid_data855 : data855.Valid src855 dst855 Finset.univ := by decide +kernel

def src856 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst856 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle856_0 : CycleData E W := ⟨9,![4,18,8,2,17,16,10,13,12,6,5],![2,8,18,3,6,38,26,4,28,14,16]⟩
def cycle856_1 : CycleData E W := ⟨9,![0,1,7,11,15,14,3,21,20,19,9],![2,4,3,14,26,16,6,8,28,38,18]⟩
def data856 : PartitionData E W := ⟨2,![cycle856_0,cycle856_1]⟩
lemma valid_data856 : data856.Valid src856 dst856 Finset.univ := by decide +kernel

def src857 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst857 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle857_0 : CycleData E W := ⟨9,![5,6,11,16,17,3,18,13,1,8,9],![2,16,14,26,38,6,8,28,4,3,18]⟩
def cycle857_1 : CycleData E W := ⟨9,![0,10,15,14,2,7,12,19,20,21,4],![2,4,26,16,6,3,14,28,18,38,8]⟩
def data857 : PartitionData E W := ⟨2,![cycle857_0,cycle857_1]⟩
lemma valid_data857 : data857.Valid src857 dst857 Finset.univ := by decide +kernel

def src858 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst858 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle858_0 : CycleData E W := ⟨9,![5,15,16,11,12,13,1,2,3,18,9],![2,16,38,26,14,28,4,3,6,8,18]⟩
def cycle858_1 : CycleData E W := ⟨9,![0,10,17,14,6,7,8,19,20,21,4],![2,4,26,6,16,14,3,18,28,38,8]⟩
def data858 : PartitionData E W := ⟨2,![cycle858_0,cycle858_1]⟩
lemma valid_data858 : data858.Valid src858 dst858 Finset.univ := by decide +kernel

def src859 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst859 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle859_0 : CycleData E W := ⟨9,![5,15,16,11,12,13,1,2,3,18,9],![2,16,38,26,14,28,4,3,6,8,18]⟩
def cycle859_1 : CycleData E W := ⟨9,![0,10,17,14,6,7,8,19,20,21,4],![2,4,26,6,16,14,3,18,38,28,8]⟩
def data859 : PartitionData E W := ⟨2,![cycle859_0,cycle859_1]⟩
lemma valid_data859 : data859.Valid src859 dst859 Finset.univ := by decide +kernel

def src860 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst860 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle860_0 : CycleData E W := ⟨9,![0,10,16,15,6,12,18,3,2,8,9],![2,4,26,38,16,14,28,8,6,3,18]⟩
def cycle860_1 : CycleData E W := ⟨9,![4,21,20,19,13,1,7,11,17,14,5],![2,8,38,18,28,4,3,14,26,6,16]⟩
def data860 : PartitionData E W := ⟨2,![cycle860_0,cycle860_1]⟩
lemma valid_data860 : data860.Valid src860 dst860 Finset.univ := by decide +kernel

def src861 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst861 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle861_0 : CycleData E W := ⟨2,![0,10,15,5],![2,4,26,16]⟩
def cycle861_1 : CycleData E W := ⟨2,![1,13,19,8],![3,4,28,18]⟩
def cycle861_2 : CycleData E W := ⟨2,![2,14,11,7],![3,6,26,14]⟩
def cycle861_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle861_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle861_5 : CycleData E W := ⟨2,![6,16,20,12],![14,16,38,28]⟩
def data861 : PartitionData E W := ⟨6,![cycle861_0,cycle861_1,cycle861_2,cycle861_3,cycle861_4,cycle861_5]⟩
lemma valid_data861 : data861.Valid src861 dst861 Finset.univ := by decide +kernel

def src862 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst862 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle862_0 : CycleData E W := ⟨9,![4,18,8,1,13,12,11,14,17,16,5],![2,8,18,3,4,28,14,26,6,38,16]⟩
def cycle862_1 : CycleData E W := ⟨9,![0,10,15,6,7,2,3,21,20,19,9],![2,4,26,16,14,3,6,8,28,38,18]⟩
def data862 : PartitionData E W := ⟨2,![cycle862_0,cycle862_1]⟩
lemma valid_data862 : data862.Valid src862 dst862 Finset.univ := by decide +kernel

def src863 : E → W := ![2,4,3,6,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst863 : E → W := ![4,3,6,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle863_0 : CycleData E W := ⟨2,![0,13,18,4],![2,4,28,8]⟩
def cycle863_1 : CycleData E W := ⟨2,![1,10,14,2],![3,4,26,6]⟩
def cycle863_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle863_3 : CycleData E W := ⟨2,![5,16,20,9],![2,16,38,18]⟩
def cycle863_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle863_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data863 : PartitionData E W := ⟨6,![cycle863_0,cycle863_1,cycle863_2,cycle863_3,cycle863_4,cycle863_5]⟩
lemma valid_data863 : data863.Valid src863 dst863 Finset.univ := by decide +kernel

def src864 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst864 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle864_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle864_1 : CycleData E W := ⟨4,![2,18,19,13,10,6],![3,8,18,28,4,14]⟩
def cycle864_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle864_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle864_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle864_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data864 : PartitionData E W := ⟨6,![cycle864_0,cycle864_1,cycle864_2,cycle864_3,cycle864_4,cycle864_5]⟩
lemma valid_data864 : data864.Valid src864 dst864 Finset.univ := by decide +kernel

def src865 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst865 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle865_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle865_1 : CycleData E W := ⟨3,![2,21,13,10,6],![3,8,28,4,14]⟩
def cycle865_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle865_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle865_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle865_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data865 : PartitionData E W := ⟨6,![cycle865_0,cycle865_1,cycle865_2,cycle865_3,cycle865_4,cycle865_5]⟩
lemma valid_data865 : data865.Valid src865 dst865 Finset.univ := by decide +kernel

def src866 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst866 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle866_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle866_1 : CycleData E W := ⟨3,![2,18,13,10,6],![3,8,28,4,14]⟩
def cycle866_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle866_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle866_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle866_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data866 : PartitionData E W := ⟨6,![cycle866_0,cycle866_1,cycle866_2,cycle866_3,cycle866_4,cycle866_5]⟩
lemma valid_data866 : data866.Valid src866 dst866 Finset.univ := by decide +kernel

def src867 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst867 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle867_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle867_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle867_2 : CycleData E W := ⟨2,![4,3,2,5],![2,6,8,3]⟩
def cycle867_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle867_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle867_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data867 : PartitionData E W := ⟨6,![cycle867_0,cycle867_1,cycle867_2,cycle867_3,cycle867_4,cycle867_5]⟩
lemma valid_data867 : data867.Valid src867 dst867 Finset.univ := by decide +kernel

def src868 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst868 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle868_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle868_1 : CycleData E W := ⟨3,![2,21,13,10,6],![3,8,28,4,14]⟩
def cycle868_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle868_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle868_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle868_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data868 : PartitionData E W := ⟨6,![cycle868_0,cycle868_1,cycle868_2,cycle868_3,cycle868_4,cycle868_5]⟩
lemma valid_data868 : data868.Valid src868 dst868 Finset.univ := by decide +kernel

def src869 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst869 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle869_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle869_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle869_2 : CycleData E W := ⟨2,![4,3,2,5],![2,6,8,3]⟩
def cycle869_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle869_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle869_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data869 : PartitionData E W := ⟨6,![cycle869_0,cycle869_1,cycle869_2,cycle869_3,cycle869_4,cycle869_5]⟩
lemma valid_data869 : data869.Valid src869 dst869 Finset.univ := by decide +kernel

def src870 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst870 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle870_0 : CycleData E W := ⟨3,![0,13,12,14,4],![2,4,28,26,6]⟩
def cycle870_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle870_2 : CycleData E W := ⟨2,![5,2,18,9],![2,3,8,18]⟩
def cycle870_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle870_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle870_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data870 : PartitionData E W := ⟨6,![cycle870_0,cycle870_1,cycle870_2,cycle870_3,cycle870_4,cycle870_5]⟩
lemma valid_data870 : data870.Valid src870 dst870 Finset.univ := by decide +kernel

def src871 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst871 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle871_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle871_1 : CycleData E W := ⟨3,![2,21,13,10,6],![3,8,28,4,14]⟩
def cycle871_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle871_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle871_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle871_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data871 : PartitionData E W := ⟨6,![cycle871_0,cycle871_1,cycle871_2,cycle871_3,cycle871_4,cycle871_5]⟩
lemma valid_data871 : data871.Valid src871 dst871 Finset.univ := by decide +kernel

def src872 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst872 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle872_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle872_1 : CycleData E W := ⟨3,![2,18,13,10,6],![3,8,28,4,14]⟩
def cycle872_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle872_3 : CycleData E W := ⟨3,![4,14,12,19,9],![2,6,26,28,18]⟩
def cycle872_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle872_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data872 : PartitionData E W := ⟨6,![cycle872_0,cycle872_1,cycle872_2,cycle872_3,cycle872_4,cycle872_5]⟩
lemma valid_data872 : data872.Valid src872 dst872 Finset.univ := by decide +kernel

def src873 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst873 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle873_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle873_1 : CycleData E W := ⟨3,![2,18,19,11,6],![3,8,18,28,14]⟩
def cycle873_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle873_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle873_4 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle873_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data873 : PartitionData E W := ⟨6,![cycle873_0,cycle873_1,cycle873_2,cycle873_3,cycle873_4,cycle873_5]⟩
lemma valid_data873 : data873.Valid src873 dst873 Finset.univ := by decide +kernel

def src874 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst874 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle874_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle874_1 : CycleData E W := ⟨2,![2,21,11,6],![3,8,28,14]⟩
def cycle874_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle874_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle874_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle874_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data874 : PartitionData E W := ⟨6,![cycle874_0,cycle874_1,cycle874_2,cycle874_3,cycle874_4,cycle874_5]⟩
lemma valid_data874 : data874.Valid src874 dst874 Finset.univ := by decide +kernel

def src875 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst875 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle875_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle875_1 : CycleData E W := ⟨2,![2,18,11,6],![3,8,28,14]⟩
def cycle875_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle875_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle875_4 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle875_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data875 : PartitionData E W := ⟨6,![cycle875_0,cycle875_1,cycle875_2,cycle875_3,cycle875_4,cycle875_5]⟩
lemma valid_data875 : data875.Valid src875 dst875 Finset.univ := by decide +kernel

def src876 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst876 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle876_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle876_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle876_2 : CycleData E W := ⟨2,![5,2,18,9],![2,3,8,18]⟩
def cycle876_3 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle876_4 : CycleData E W := ⟨2,![7,8,19,11],![14,16,18,28]⟩
def cycle876_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data876 : PartitionData E W := ⟨6,![cycle876_0,cycle876_1,cycle876_2,cycle876_3,cycle876_4,cycle876_5]⟩
lemma valid_data876 : data876.Valid src876 dst876 Finset.univ := by decide +kernel

def src877 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst877 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle877_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle877_1 : CycleData E W := ⟨2,![2,21,11,6],![3,8,28,14]⟩
def cycle877_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle877_3 : CycleData E W := ⟨3,![10,7,14,17,13],![4,14,16,6,26]⟩
def cycle877_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle877_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data877 : PartitionData E W := ⟨6,![cycle877_0,cycle877_1,cycle877_2,cycle877_3,cycle877_4,cycle877_5]⟩
lemma valid_data877 : data877.Valid src877 dst877 Finset.univ := by decide +kernel

def src878 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst878 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle878_0 : CycleData E W := ⟨9,![4,3,18,11,6,1,13,16,15,8,9],![2,6,8,28,14,3,4,26,38,16,18]⟩
def cycle878_1 : CycleData E W := ⟨9,![0,10,7,14,17,12,19,20,21,2,5],![2,4,14,16,6,26,28,18,38,8,3]⟩
def data878 : PartitionData E W := ⟨2,![cycle878_0,cycle878_1]⟩
lemma valid_data878 : data878.Valid src878 dst878 Finset.univ := by decide +kernel

def src879 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst879 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle879_0 : CycleData E W := ⟨2,![0,13,14,4],![2,4,26,6]⟩
def cycle879_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle879_2 : CycleData E W := ⟨2,![5,2,18,9],![2,3,8,18]⟩
def cycle879_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle879_4 : CycleData E W := ⟨2,![7,15,12,11],![14,16,26,28]⟩
def cycle879_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data879 : PartitionData E W := ⟨6,![cycle879_0,cycle879_1,cycle879_2,cycle879_3,cycle879_4,cycle879_5]⟩
lemma valid_data879 : data879.Valid src879 dst879 Finset.univ := by decide +kernel

def src880 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst880 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle880_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle880_1 : CycleData E W := ⟨2,![2,21,11,6],![3,8,28,14]⟩
def cycle880_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle880_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle880_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle880_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data880 : PartitionData E W := ⟨6,![cycle880_0,cycle880_1,cycle880_2,cycle880_3,cycle880_4,cycle880_5]⟩
lemma valid_data880 : data880.Valid src880 dst880 Finset.univ := by decide +kernel

def src881 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst881 : E → W := ![4,3,8,6,2,3,14,16,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle881_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle881_1 : CycleData E W := ⟨2,![2,18,11,6],![3,8,28,14]⟩
def cycle881_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle881_3 : CycleData E W := ⟨3,![4,14,12,19,9],![2,6,26,28,18]⟩
def cycle881_4 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle881_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data881 : PartitionData E W := ⟨6,![cycle881_0,cycle881_1,cycle881_2,cycle881_3,cycle881_4,cycle881_5]⟩
lemma valid_data881 : data881.Valid src881 dst881 Finset.univ := by decide +kernel

def src882 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst882 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle882_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle882_1 : CycleData E W := ⟨3,![2,18,19,12,6],![3,8,18,28,14]⟩
def cycle882_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle882_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle882_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle882_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data882 : PartitionData E W := ⟨6,![cycle882_0,cycle882_1,cycle882_2,cycle882_3,cycle882_4,cycle882_5]⟩
lemma valid_data882 : data882.Valid src882 dst882 Finset.univ := by decide +kernel

def src883 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst883 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle883_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle883_1 : CycleData E W := ⟨2,![2,21,12,6],![3,8,28,14]⟩
def cycle883_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle883_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle883_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle883_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data883 : PartitionData E W := ⟨6,![cycle883_0,cycle883_1,cycle883_2,cycle883_3,cycle883_4,cycle883_5]⟩
lemma valid_data883 : data883.Valid src883 dst883 Finset.univ := by decide +kernel

def src884 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst884 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle884_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle884_1 : CycleData E W := ⟨2,![2,18,12,6],![3,8,28,14]⟩
def cycle884_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle884_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle884_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle884_5 : CycleData E W := ⟨3,![10,16,20,19,13],![4,26,38,18,28]⟩
def data884 : PartitionData E W := ⟨6,![cycle884_0,cycle884_1,cycle884_2,cycle884_3,cycle884_4,cycle884_5]⟩
lemma valid_data884 : data884.Valid src884 dst884 Finset.univ := by decide +kernel

def src885 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst885 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle885_0 : CycleData E W := ⟨9,![4,3,18,8,15,16,11,12,13,1,5],![2,6,8,18,16,38,26,14,28,4,3]⟩
def cycle885_1 : CycleData E W := ⟨9,![0,10,17,14,7,6,2,21,20,19,9],![2,4,26,6,16,14,3,8,38,28,18]⟩
def data885 : PartitionData E W := ⟨2,![cycle885_0,cycle885_1]⟩
lemma valid_data885 : data885.Valid src885 dst885 Finset.univ := by decide +kernel

def src886 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst886 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle886_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle886_1 : CycleData E W := ⟨2,![2,21,12,6],![3,8,28,14]⟩
def cycle886_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle886_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle886_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle886_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data886 : PartitionData E W := ⟨6,![cycle886_0,cycle886_1,cycle886_2,cycle886_3,cycle886_4,cycle886_5]⟩
lemma valid_data886 : data886.Valid src886 dst886 Finset.univ := by decide +kernel

def src887 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst887 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle887_0 : CycleData E W := ⟨9,![4,3,18,13,1,6,11,16,15,8,9],![2,6,8,28,4,3,14,26,38,16,18]⟩
def cycle887_1 : CycleData E W := ⟨9,![0,10,17,14,7,12,19,20,21,2,5],![2,4,26,6,16,14,28,18,38,8,3]⟩
def data887 : PartitionData E W := ⟨2,![cycle887_0,cycle887_1]⟩
lemma valid_data887 : data887.Valid src887 dst887 Finset.univ := by decide +kernel

def src888 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst888 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle888_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle888_1 : CycleData E W := ⟨2,![1,13,12,6],![3,4,28,14]⟩
def cycle888_2 : CycleData E W := ⟨2,![5,2,18,9],![2,3,8,18]⟩
def cycle888_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle888_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle888_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data888 : PartitionData E W := ⟨6,![cycle888_0,cycle888_1,cycle888_2,cycle888_3,cycle888_4,cycle888_5]⟩
lemma valid_data888 : data888.Valid src888 dst888 Finset.univ := by decide +kernel

def src889 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst889 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle889_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle889_1 : CycleData E W := ⟨2,![2,21,12,6],![3,8,28,14]⟩
def cycle889_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle889_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle889_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle889_5 : CycleData E W := ⟨3,![10,14,17,20,13],![4,26,6,38,28]⟩
def data889 : PartitionData E W := ⟨6,![cycle889_0,cycle889_1,cycle889_2,cycle889_3,cycle889_4,cycle889_5]⟩
lemma valid_data889 : data889.Valid src889 dst889 Finset.univ := by decide +kernel

def src890 : E → W := ![2,4,3,8,6,2,3,14,16,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst890 : E → W := ![4,3,8,6,2,3,14,16,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle890_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle890_1 : CycleData E W := ⟨2,![2,18,12,6],![3,8,28,14]⟩
def cycle890_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle890_3 : CycleData E W := ⟨4,![4,14,10,13,19,9],![2,6,26,4,28,18]⟩
def cycle890_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle890_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data890 : PartitionData E W := ⟨6,![cycle890_0,cycle890_1,cycle890_2,cycle890_3,cycle890_4,cycle890_5]⟩
lemma valid_data890 : data890.Valid src890 dst890 Finset.univ := by decide +kernel

def src891 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst891 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle891_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle891_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle891_2 : CycleData E W := ⟨3,![4,17,21,18,9],![2,6,38,8,18]⟩
def cycle891_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle891_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle891_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data891 : PartitionData E W := ⟨6,![cycle891_0,cycle891_1,cycle891_2,cycle891_3,cycle891_4,cycle891_5]⟩
lemma valid_data891 : data891.Valid src891 dst891 Finset.univ := by decide +kernel

def src892 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst892 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle892_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle892_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle892_2 : CycleData E W := ⟨2,![4,17,19,9],![2,6,38,18]⟩
def cycle892_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle892_4 : CycleData E W := ⟨3,![10,8,18,21,13],![4,14,18,8,28]⟩
def cycle892_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data892 : PartitionData E W := ⟨6,![cycle892_0,cycle892_1,cycle892_2,cycle892_3,cycle892_4,cycle892_5]⟩
lemma valid_data892 : data892.Valid src892 dst892 Finset.univ := by decide +kernel

def src893 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst893 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle893_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle893_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle893_2 : CycleData E W := ⟨2,![4,17,20,9],![2,6,38,18]⟩
def cycle893_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle893_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle893_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data893 : PartitionData E W := ⟨6,![cycle893_0,cycle893_1,cycle893_2,cycle893_3,cycle893_4,cycle893_5]⟩
lemma valid_data893 : data893.Valid src893 dst893 Finset.univ := by decide +kernel

def src894 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst894 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle894_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle894_1 : CycleData E W := ⟨2,![2,21,15,6],![3,8,38,16]⟩
def cycle894_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle894_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle894_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle894_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data894 : PartitionData E W := ⟨6,![cycle894_0,cycle894_1,cycle894_2,cycle894_3,cycle894_4,cycle894_5]⟩
lemma valid_data894 : data894.Valid src894 dst894 Finset.univ := by decide +kernel

def src895 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst895 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle895_0 : CycleData E W := ⟨9,![4,3,18,8,7,15,16,12,13,1,5],![2,6,8,18,14,16,38,26,28,4,3]⟩
def cycle895_1 : CycleData E W := ⟨9,![0,10,11,17,14,6,2,21,20,19,9],![2,4,14,26,6,16,3,8,28,38,18]⟩
def data895 : PartitionData E W := ⟨2,![cycle895_0,cycle895_1]⟩
lemma valid_data895 : data895.Valid src895 dst895 Finset.univ := by decide +kernel

def src896 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst896 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle896_0 : CycleData E W := ⟨9,![4,3,18,13,1,6,15,16,11,8,9],![2,6,8,28,4,3,16,38,26,14,18]⟩
def cycle896_1 : CycleData E W := ⟨9,![0,10,7,14,17,12,19,20,21,2,5],![2,4,14,16,6,26,28,18,38,8,3]⟩
def data896 : PartitionData E W := ⟨2,![cycle896_0,cycle896_1]⟩
lemma valid_data896 : data896.Valid src896 dst896 Finset.univ := by decide +kernel

def src897 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst897 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle897_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle897_1 : CycleData E W := ⟨2,![2,21,16,6],![3,8,38,16]⟩
def cycle897_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle897_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle897_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle897_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data897 : PartitionData E W := ⟨6,![cycle897_0,cycle897_1,cycle897_2,cycle897_3,cycle897_4,cycle897_5]⟩
lemma valid_data897 : data897.Valid src897 dst897 Finset.univ := by decide +kernel

def src898 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst898 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle898_0 : CycleData E W := ⟨9,![0,13,12,11,8,18,2,6,16,17,4],![2,4,28,26,14,18,8,3,16,38,6]⟩
def cycle898_1 : CycleData E W := ⟨9,![5,1,10,7,15,14,3,21,20,19,9],![2,3,4,14,16,26,6,8,28,38,18]⟩
def data898 : PartitionData E W := ⟨2,![cycle898_0,cycle898_1]⟩
lemma valid_data898 : data898.Valid src898 dst898 Finset.univ := by decide +kernel

def src899 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst899 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle899_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle899_1 : CycleData E W := ⟨2,![2,21,16,6],![3,8,38,16]⟩
def cycle899_2 : CycleData E W := ⟨2,![3,18,12,14],![6,8,28,26]⟩
def cycle899_3 : CycleData E W := ⟨2,![4,17,20,9],![2,6,38,18]⟩
def cycle899_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle899_5 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def data899 : PartitionData E W := ⟨6,![cycle899_0,cycle899_1,cycle899_2,cycle899_3,cycle899_4,cycle899_5]⟩
lemma valid_data899 : data899.Valid src899 dst899 Finset.univ := by decide +kernel

def src900 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst900 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle900_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle900_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle900_2 : CycleData E W := ⟨3,![4,17,21,18,9],![2,6,38,8,18]⟩
def cycle900_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle900_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle900_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data900 : PartitionData E W := ⟨6,![cycle900_0,cycle900_1,cycle900_2,cycle900_3,cycle900_4,cycle900_5]⟩
lemma valid_data900 : data900.Valid src900 dst900 Finset.univ := by decide +kernel

def src901 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst901 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle901_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle901_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle901_2 : CycleData E W := ⟨2,![4,17,19,9],![2,6,38,18]⟩
def cycle901_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle901_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle901_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data901 : PartitionData E W := ⟨6,![cycle901_0,cycle901_1,cycle901_2,cycle901_3,cycle901_4,cycle901_5]⟩
lemma valid_data901 : data901.Valid src901 dst901 Finset.univ := by decide +kernel

def src902 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst902 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle902_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle902_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle902_2 : CycleData E W := ⟨2,![4,17,20,9],![2,6,38,18]⟩
def cycle902_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle902_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle902_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data902 : PartitionData E W := ⟨6,![cycle902_0,cycle902_1,cycle902_2,cycle902_3,cycle902_4,cycle902_5]⟩
lemma valid_data902 : data902.Valid src902 dst902 Finset.univ := by decide +kernel

def src903 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst903 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle903_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle903_1 : CycleData E W := ⟨2,![2,21,15,6],![3,8,38,16]⟩
def cycle903_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle903_3 : CycleData E W := ⟨3,![10,7,14,17,13],![4,14,16,6,26]⟩
def cycle903_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle903_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data903 : PartitionData E W := ⟨6,![cycle903_0,cycle903_1,cycle903_2,cycle903_3,cycle903_4,cycle903_5]⟩
lemma valid_data903 : data903.Valid src903 dst903 Finset.univ := by decide +kernel

def src904 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst904 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle904_0 : CycleData E W := ⟨9,![0,1,2,18,8,11,12,16,15,14,4],![2,4,3,8,18,14,28,26,38,16,6]⟩
def cycle904_1 : CycleData E W := ⟨9,![5,6,7,10,13,17,3,21,20,19,9],![2,3,16,14,4,26,6,8,28,38,18]⟩
def data904 : PartitionData E W := ⟨2,![cycle904_0,cycle904_1]⟩
lemma valid_data904 : data904.Valid src904 dst904 Finset.univ := by decide +kernel

def src905 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst905 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle905_0 : CycleData E W := ⟨9,![4,3,18,12,16,15,6,1,10,8,9],![2,6,8,28,26,38,16,3,4,14,18]⟩
def cycle905_1 : CycleData E W := ⟨9,![0,13,17,14,7,11,19,20,21,2,5],![2,4,26,6,16,14,28,18,38,8,3]⟩
def data905 : PartitionData E W := ⟨2,![cycle905_0,cycle905_1]⟩
lemma valid_data905 : data905.Valid src905 dst905 Finset.univ := by decide +kernel

def src906 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst906 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle906_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle906_1 : CycleData E W := ⟨2,![2,21,16,6],![3,8,38,16]⟩
def cycle906_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle906_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle906_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle906_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data906 : PartitionData E W := ⟨6,![cycle906_0,cycle906_1,cycle906_2,cycle906_3,cycle906_4,cycle906_5]⟩
lemma valid_data906 : data906.Valid src906 dst906 Finset.univ := by decide +kernel

def src907 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst907 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle907_0 : CycleData E W := ⟨9,![0,13,12,11,8,18,2,6,16,17,4],![2,4,26,28,14,18,8,3,16,38,6]⟩
def cycle907_1 : CycleData E W := ⟨9,![5,1,10,7,15,14,3,21,20,19,9],![2,3,4,14,16,26,6,8,28,38,18]⟩
def data907 : PartitionData E W := ⟨2,![cycle907_0,cycle907_1]⟩
lemma valid_data907 : data907.Valid src907 dst907 Finset.univ := by decide +kernel

def src908 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst908 : E → W := ![4,3,8,6,2,3,16,14,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle908_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle908_1 : CycleData E W := ⟨2,![2,21,16,6],![3,8,38,16]⟩
def cycle908_2 : CycleData E W := ⟨2,![3,18,12,14],![6,8,28,26]⟩
def cycle908_3 : CycleData E W := ⟨2,![4,17,20,9],![2,6,38,18]⟩
def cycle908_4 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle908_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data908 : PartitionData E W := ⟨6,![cycle908_0,cycle908_1,cycle908_2,cycle908_3,cycle908_4,cycle908_5]⟩
lemma valid_data908 : data908.Valid src908 dst908 Finset.univ := by decide +kernel

def src909 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst909 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle909_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle909_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle909_2 : CycleData E W := ⟨3,![4,17,21,18,9],![2,6,38,8,18]⟩
def cycle909_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle909_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle909_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data909 : PartitionData E W := ⟨6,![cycle909_0,cycle909_1,cycle909_2,cycle909_3,cycle909_4,cycle909_5]⟩
lemma valid_data909 : data909.Valid src909 dst909 Finset.univ := by decide +kernel

def src910 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst910 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle910_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle910_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle910_2 : CycleData E W := ⟨2,![4,17,19,9],![2,6,38,18]⟩
def cycle910_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle910_4 : CycleData E W := ⟨2,![18,8,12,21],![8,18,14,28]⟩
def cycle910_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data910 : PartitionData E W := ⟨6,![cycle910_0,cycle910_1,cycle910_2,cycle910_3,cycle910_4,cycle910_5]⟩
lemma valid_data910 : data910.Valid src910 dst910 Finset.univ := by decide +kernel

def src911 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst911 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle911_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle911_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle911_2 : CycleData E W := ⟨2,![4,17,20,9],![2,6,38,18]⟩
def cycle911_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle911_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle911_5 : CycleData E W := ⟨3,![10,16,21,18,13],![4,26,38,8,28]⟩
def data911 : PartitionData E W := ⟨6,![cycle911_0,cycle911_1,cycle911_2,cycle911_3,cycle911_4,cycle911_5]⟩
lemma valid_data911 : data911.Valid src911 dst911 Finset.univ := by decide +kernel

def src912 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst912 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle912_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle912_1 : CycleData E W := ⟨2,![2,21,15,6],![3,8,38,16]⟩
def cycle912_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle912_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle912_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle912_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data912 : PartitionData E W := ⟨6,![cycle912_0,cycle912_1,cycle912_2,cycle912_3,cycle912_4,cycle912_5]⟩
lemma valid_data912 : data912.Valid src912 dst912 Finset.univ := by decide +kernel

def src913 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst913 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle913_0 : CycleData E W := ⟨9,![4,14,15,16,10,13,12,8,18,2,5],![2,6,16,38,26,4,28,14,18,8,3]⟩
def cycle913_1 : CycleData E W := ⟨9,![0,1,6,7,11,17,3,21,20,19,9],![2,4,3,16,14,26,6,8,28,38,18]⟩
def data913 : PartitionData E W := ⟨2,![cycle913_0,cycle913_1]⟩
lemma valid_data913 : data913.Valid src913 dst913 Finset.univ := by decide +kernel

def src914 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst914 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle914_0 : CycleData E W := ⟨9,![4,3,18,13,1,6,15,16,11,8,9],![2,6,8,28,4,3,16,38,26,14,18]⟩
def cycle914_1 : CycleData E W := ⟨9,![0,10,17,14,7,12,19,20,21,2,5],![2,4,26,6,16,14,28,18,38,8,3]⟩
def data914 : PartitionData E W := ⟨2,![cycle914_0,cycle914_1]⟩
lemma valid_data914 : data914.Valid src914 dst914 Finset.univ := by decide +kernel

def src915 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst915 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle915_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle915_1 : CycleData E W := ⟨2,![2,21,16,6],![3,8,38,16]⟩
def cycle915_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle915_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle915_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle915_5 : CycleData E W := ⟨3,![10,14,17,20,13],![4,26,6,38,28]⟩
def data915 : PartitionData E W := ⟨6,![cycle915_0,cycle915_1,cycle915_2,cycle915_3,cycle915_4,cycle915_5]⟩
lemma valid_data915 : data915.Valid src915 dst915 Finset.univ := by decide +kernel

def src916 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst916 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle916_0 : CycleData E W := ⟨9,![0,13,12,11,14,17,16,6,2,18,9],![2,4,28,14,26,6,38,16,3,8,18]⟩
def cycle916_1 : CycleData E W := ⟨9,![4,3,21,20,19,8,7,15,10,1,5],![2,6,8,28,38,18,14,16,26,4,3]⟩
def data916 : PartitionData E W := ⟨2,![cycle916_0,cycle916_1]⟩
lemma valid_data916 : data916.Valid src916 dst916 Finset.univ := by decide +kernel

def src917 : E → W := ![2,4,3,8,6,2,3,16,14,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst917 : E → W := ![4,3,8,6,2,3,16,14,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle917_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle917_1 : CycleData E W := ⟨2,![2,21,16,6],![3,8,38,16]⟩
def cycle917_2 : CycleData E W := ⟨3,![10,14,3,18,13],![4,26,6,8,28]⟩
def cycle917_3 : CycleData E W := ⟨2,![4,17,20,9],![2,6,38,18]⟩
def cycle917_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle917_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data917 : PartitionData E W := ⟨6,![cycle917_0,cycle917_1,cycle917_2,cycle917_3,cycle917_4,cycle917_5]⟩
lemma valid_data917 : data917.Valid src917 dst917 Finset.univ := by decide +kernel

def src918 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,16,26,38,8,18,28,38]
def dst918 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle918_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle918_1 : CycleData E W := ⟨2,![2,18,7,6],![3,8,18,16]⟩
def cycle918_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle918_3 : CycleData E W := ⟨3,![4,14,15,11,9],![2,6,16,26,14]⟩
def cycle918_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle918_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data918 : PartitionData E W := ⟨6,![cycle918_0,cycle918_1,cycle918_2,cycle918_3,cycle918_4,cycle918_5]⟩
lemma valid_data918 : data918.Valid src918 dst918 Finset.univ := by decide +kernel

def src919 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,16,26,38,8,18,38,28]
def dst919 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle919_0 : CycleData E W := ⟨1,![0,10,9],![2,4,14]⟩
def cycle919_1 : CycleData E W := ⟨2,![1,13,21,2],![3,4,28,8]⟩
def cycle919_2 : CycleData E W := ⟨2,![3,18,19,17],![6,8,18,38]⟩
def cycle919_3 : CycleData E W := ⟨2,![4,14,6,5],![2,6,16,3]⟩
def cycle919_4 : CycleData E W := ⟨2,![8,7,15,11],![14,18,16,26]⟩
def cycle919_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data919 : PartitionData E W := ⟨6,![cycle919_0,cycle919_1,cycle919_2,cycle919_3,cycle919_4,cycle919_5]⟩
lemma valid_data919 : data919.Valid src919 dst919 Finset.univ := by decide +kernel

def src920 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,16,26,38,8,28,18,38]
def dst920 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle920_0 : CycleData E W := ⟨1,![0,10,9],![2,4,14]⟩
def cycle920_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle920_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle920_3 : CycleData E W := ⟨2,![4,14,6,5],![2,6,16,3]⟩
def cycle920_4 : CycleData E W := ⟨2,![8,7,15,11],![14,18,16,26]⟩
def cycle920_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data920 : PartitionData E W := ⟨6,![cycle920_0,cycle920_1,cycle920_2,cycle920_3,cycle920_4,cycle920_5]⟩
lemma valid_data920 : data920.Valid src920 dst920 Finset.univ := by decide +kernel

def src921 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,16,38,26,8,18,28,38]
def dst921 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle921_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle921_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle921_2 : CycleData E W := ⟨2,![4,17,11,9],![2,6,26,14]⟩
def cycle921_3 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle921_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle921_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data921 : PartitionData E W := ⟨6,![cycle921_0,cycle921_1,cycle921_2,cycle921_3,cycle921_4,cycle921_5]⟩
lemma valid_data921 : data921.Valid src921 dst921 Finset.univ := by decide +kernel

def src922 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,16,38,26,8,18,38,28]
def dst922 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle922_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle922_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle922_2 : CycleData E W := ⟨2,![4,17,11,9],![2,6,26,14]⟩
def cycle922_3 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle922_4 : CycleData E W := ⟨3,![10,8,18,21,13],![4,14,18,8,28]⟩
def cycle922_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data922 : PartitionData E W := ⟨6,![cycle922_0,cycle922_1,cycle922_2,cycle922_3,cycle922_4,cycle922_5]⟩
lemma valid_data922 : data922.Valid src922 dst922 Finset.univ := by decide +kernel

def src923 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,16,38,26,8,28,18,38]
def dst923 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle923_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle923_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle923_2 : CycleData E W := ⟨2,![4,17,11,9],![2,6,26,14]⟩
def cycle923_3 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle923_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle923_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data923 : PartitionData E W := ⟨6,![cycle923_0,cycle923_1,cycle923_2,cycle923_3,cycle923_4,cycle923_5]⟩
lemma valid_data923 : data923.Valid src923 dst923 Finset.univ := by decide +kernel

def src924 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,26,16,38,8,18,28,38]
def dst924 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle924_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle924_1 : CycleData E W := ⟨2,![2,18,7,6],![3,8,18,16]⟩
def cycle924_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle924_3 : CycleData E W := ⟨2,![4,14,11,9],![2,6,26,14]⟩
def cycle924_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle924_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data924 : PartitionData E W := ⟨6,![cycle924_0,cycle924_1,cycle924_2,cycle924_3,cycle924_4,cycle924_5]⟩
lemma valid_data924 : data924.Valid src924 dst924 Finset.univ := by decide +kernel

def src925 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,26,16,38,8,18,38,28]
def dst925 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle925_0 : CycleData E W := ⟨9,![0,13,12,11,8,18,3,17,16,6,5],![2,4,28,26,14,18,8,6,38,16,3]⟩
def cycle925_1 : CycleData E W := ⟨9,![4,14,15,7,19,20,21,2,1,10,9],![2,6,26,16,18,38,28,8,3,4,14]⟩
def data925 : PartitionData E W := ⟨2,![cycle925_0,cycle925_1]⟩
lemma valid_data925 : data925.Valid src925 dst925 Finset.univ := by decide +kernel

def src926 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,26,28,6,26,16,38,8,28,18,38]
def dst926 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle926_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle926_1 : CycleData E W := ⟨3,![2,18,12,15,6],![3,8,28,26,16]⟩
def cycle926_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle926_3 : CycleData E W := ⟨2,![4,14,11,9],![2,6,26,14]⟩
def cycle926_4 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle926_5 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def data926 : PartitionData E W := ⟨6,![cycle926_0,cycle926_1,cycle926_2,cycle926_3,cycle926_4,cycle926_5]⟩
lemma valid_data926 : data926.Valid src926 dst926 Finset.univ := by decide +kernel

def src927 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,16,26,38,8,18,28,38]
def dst927 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle927_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle927_1 : CycleData E W := ⟨2,![2,18,7,6],![3,8,18,16]⟩
def cycle927_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle927_3 : CycleData E W := ⟨4,![4,14,15,13,10,9],![2,6,16,26,4,14]⟩
def cycle927_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle927_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data927 : PartitionData E W := ⟨6,![cycle927_0,cycle927_1,cycle927_2,cycle927_3,cycle927_4,cycle927_5]⟩
lemma valid_data927 : data927.Valid src927 dst927 Finset.univ := by decide +kernel

def src928 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,16,26,38,8,18,38,28]
def dst928 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle928_0 : CycleData E W := ⟨1,![0,10,9],![2,4,14]⟩
def cycle928_1 : CycleData E W := ⟨2,![1,13,15,6],![3,4,26,16]⟩
def cycle928_2 : CycleData E W := ⟨2,![4,3,2,5],![2,6,8,3]⟩
def cycle928_3 : CycleData E W := ⟨2,![14,7,19,17],![6,16,18,38]⟩
def cycle928_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle928_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data928 : PartitionData E W := ⟨6,![cycle928_0,cycle928_1,cycle928_2,cycle928_3,cycle928_4,cycle928_5]⟩
lemma valid_data928 : data928.Valid src928 dst928 Finset.univ := by decide +kernel

def src929 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,16,26,38,8,28,18,38]
def dst929 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle929_0 : CycleData E W := ⟨1,![0,10,9],![2,4,14]⟩
def cycle929_1 : CycleData E W := ⟨2,![1,13,15,6],![3,4,26,16]⟩
def cycle929_2 : CycleData E W := ⟨2,![4,3,2,5],![2,6,8,3]⟩
def cycle929_3 : CycleData E W := ⟨2,![14,7,20,17],![6,16,18,38]⟩
def cycle929_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle929_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data929 : PartitionData E W := ⟨6,![cycle929_0,cycle929_1,cycle929_2,cycle929_3,cycle929_4,cycle929_5]⟩
lemma valid_data929 : data929.Valid src929 dst929 Finset.univ := by decide +kernel

def src930 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,16,38,26,8,18,28,38]
def dst930 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle930_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle930_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle930_2 : CycleData E W := ⟨3,![4,17,13,10,9],![2,6,26,4,14]⟩
def cycle930_3 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle930_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle930_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data930 : PartitionData E W := ⟨6,![cycle930_0,cycle930_1,cycle930_2,cycle930_3,cycle930_4,cycle930_5]⟩
lemma valid_data930 : data930.Valid src930 dst930 Finset.univ := by decide +kernel

def src931 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,16,38,26,8,18,38,28]
def dst931 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle931_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle931_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle931_2 : CycleData E W := ⟨3,![4,17,13,10,9],![2,6,26,4,14]⟩
def cycle931_3 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle931_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle931_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data931 : PartitionData E W := ⟨6,![cycle931_0,cycle931_1,cycle931_2,cycle931_3,cycle931_4,cycle931_5]⟩
lemma valid_data931 : data931.Valid src931 dst931 Finset.univ := by decide +kernel

def src932 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,16,38,26,8,28,18,38]
def dst932 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle932_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle932_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle932_2 : CycleData E W := ⟨3,![4,17,13,10,9],![2,6,26,4,14]⟩
def cycle932_3 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle932_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle932_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data932 : PartitionData E W := ⟨6,![cycle932_0,cycle932_1,cycle932_2,cycle932_3,cycle932_4,cycle932_5]⟩
lemma valid_data932 : data932.Valid src932 dst932 Finset.univ := by decide +kernel

def src933 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,26,16,38,8,18,28,38]
def dst933 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle933_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle933_1 : CycleData E W := ⟨2,![2,18,7,6],![3,8,18,16]⟩
def cycle933_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle933_3 : CycleData E W := ⟨3,![4,14,13,10,9],![2,6,26,4,14]⟩
def cycle933_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle933_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data933 : PartitionData E W := ⟨6,![cycle933_0,cycle933_1,cycle933_2,cycle933_3,cycle933_4,cycle933_5]⟩
lemma valid_data933 : data933.Valid src933 dst933 Finset.univ := by decide +kernel

def src934 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,26,16,38,8,18,38,28]
def dst934 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle934_0 : CycleData E W := ⟨1,![0,10,9],![2,4,14]⟩
def cycle934_1 : CycleData E W := ⟨2,![1,13,15,6],![3,4,26,16]⟩
def cycle934_2 : CycleData E W := ⟨2,![4,3,2,5],![2,6,8,3]⟩
def cycle934_3 : CycleData E W := ⟨1,![7,19,16],![16,18,38]⟩
def cycle934_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle934_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data934 : PartitionData E W := ⟨6,![cycle934_0,cycle934_1,cycle934_2,cycle934_3,cycle934_4,cycle934_5]⟩
lemma valid_data934 : data934.Valid src934 dst934 Finset.univ := by decide +kernel

def src935 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,14,28,26,6,26,16,38,8,28,18,38]
def dst935 : E → W := ![4,3,8,6,2,3,16,18,14,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle935_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle935_1 : CycleData E W := ⟨3,![2,18,12,15,6],![3,8,28,26,16]⟩
def cycle935_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle935_3 : CycleData E W := ⟨3,![4,14,13,10,9],![2,6,26,4,14]⟩
def cycle935_4 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle935_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data935 : PartitionData E W := ⟨6,![cycle935_0,cycle935_1,cycle935_2,cycle935_3,cycle935_4,cycle935_5]⟩
lemma valid_data935 : data935.Valid src935 dst935 Finset.univ := by decide +kernel

def src936 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,16,26,38,8,18,28,38]
def dst936 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle936_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle936_1 : CycleData E W := ⟨2,![2,18,7,6],![3,8,18,16]⟩
def cycle936_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle936_3 : CycleData E W := ⟨3,![4,14,15,11,9],![2,6,16,26,14]⟩
def cycle936_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle936_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data936 : PartitionData E W := ⟨6,![cycle936_0,cycle936_1,cycle936_2,cycle936_3,cycle936_4,cycle936_5]⟩
lemma valid_data936 : data936.Valid src936 dst936 Finset.univ := by decide +kernel

def src937 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,16,26,38,8,18,38,28]
def dst937 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle937_0 : CycleData E W := ⟨9,![5,6,7,18,3,17,16,10,13,12,9],![2,3,16,18,8,6,38,26,4,28,14]⟩
def cycle937_1 : CycleData E W := ⟨9,![0,1,2,21,20,19,8,11,15,14,4],![2,4,3,8,28,38,18,14,26,16,6]⟩
def data937 : PartitionData E W := ⟨2,![cycle937_0,cycle937_1]⟩
lemma valid_data937 : data937.Valid src937 dst937 Finset.univ := by decide +kernel

def src938 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,16,26,38,8,28,18,38]
def dst938 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle938_0 : CycleData E W := ⟨2,![0,10,11,9],![2,4,26,14]⟩
def cycle938_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle938_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle938_3 : CycleData E W := ⟨2,![4,14,6,5],![2,6,16,3]⟩
def cycle938_4 : CycleData E W := ⟨2,![7,20,16,15],![16,18,38,26]⟩
def cycle938_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data938 : PartitionData E W := ⟨6,![cycle938_0,cycle938_1,cycle938_2,cycle938_3,cycle938_4,cycle938_5]⟩
lemma valid_data938 : data938.Valid src938 dst938 Finset.univ := by decide +kernel

def src939 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,16,38,26,8,18,28,38]
def dst939 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle939_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle939_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle939_2 : CycleData E W := ⟨2,![4,17,11,9],![2,6,26,14]⟩
def cycle939_3 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle939_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle939_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data939 : PartitionData E W := ⟨6,![cycle939_0,cycle939_1,cycle939_2,cycle939_3,cycle939_4,cycle939_5]⟩
lemma valid_data939 : data939.Valid src939 dst939 Finset.univ := by decide +kernel

def src940 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,16,38,26,8,18,38,28]
def dst940 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle940_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle940_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle940_2 : CycleData E W := ⟨2,![4,17,11,9],![2,6,26,14]⟩
def cycle940_3 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle940_4 : CycleData E W := ⟨2,![18,8,12,21],![8,18,14,28]⟩
def cycle940_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data940 : PartitionData E W := ⟨6,![cycle940_0,cycle940_1,cycle940_2,cycle940_3,cycle940_4,cycle940_5]⟩
lemma valid_data940 : data940.Valid src940 dst940 Finset.univ := by decide +kernel

def src941 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,16,38,26,8,28,18,38]
def dst941 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle941_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle941_1 : CycleData E W := ⟨2,![2,3,14,6],![3,8,6,16]⟩
def cycle941_2 : CycleData E W := ⟨2,![4,17,11,9],![2,6,26,14]⟩
def cycle941_3 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle941_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle941_5 : CycleData E W := ⟨3,![10,16,21,18,13],![4,26,38,8,28]⟩
def data941 : PartitionData E W := ⟨6,![cycle941_0,cycle941_1,cycle941_2,cycle941_3,cycle941_4,cycle941_5]⟩
lemma valid_data941 : data941.Valid src941 dst941 Finset.univ := by decide +kernel

def src942 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,26,16,38,8,18,28,38]
def dst942 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle942_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle942_1 : CycleData E W := ⟨2,![2,18,7,6],![3,8,18,16]⟩
def cycle942_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle942_3 : CycleData E W := ⟨2,![4,14,11,9],![2,6,26,14]⟩
def cycle942_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle942_5 : CycleData E W := ⟨3,![10,15,16,20,13],![4,26,16,38,28]⟩
def data942 : PartitionData E W := ⟨6,![cycle942_0,cycle942_1,cycle942_2,cycle942_3,cycle942_4,cycle942_5]⟩
lemma valid_data942 : data942.Valid src942 dst942 Finset.univ := by decide +kernel

def src943 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,26,16,38,8,18,38,28]
def dst943 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle943_0 : CycleData E W := ⟨9,![5,2,18,7,16,17,14,10,13,12,9],![2,3,8,18,16,38,6,26,4,28,14]⟩
def cycle943_1 : CycleData E W := ⟨9,![0,1,6,15,11,8,19,20,21,3,4],![2,4,3,16,26,14,18,38,28,8,6]⟩
def data943 : PartitionData E W := ⟨2,![cycle943_0,cycle943_1]⟩
lemma valid_data943 : data943.Valid src943 dst943 Finset.univ := by decide +kernel

def src944 : E → W := ![2,4,3,8,6,2,3,16,18,14,4,26,14,28,6,26,16,38,8,28,18,38]
def dst944 : E → W := ![4,3,8,6,2,3,16,18,14,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle944_0 : CycleData E W := ⟨1,![0,1,5],![2,4,3]⟩
def cycle944_1 : CycleData E W := ⟨4,![2,18,13,10,15,6],![3,8,28,4,26,16]⟩
def cycle944_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle944_3 : CycleData E W := ⟨2,![4,14,11,9],![2,6,26,14]⟩
def cycle944_4 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle944_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data944 : PartitionData E W := ⟨6,![cycle944_0,cycle944_1,cycle944_2,cycle944_3,cycle944_4,cycle944_5]⟩
lemma valid_data944 : data944.Valid src944 dst944 Finset.univ := by decide +kernel

def src945 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst945 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle945_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle945_1 : CycleData E W := ⟨3,![1,13,19,18,2],![3,4,28,18,8]⟩
def cycle945_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle945_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle945_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle945_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data945 : PartitionData E W := ⟨6,![cycle945_0,cycle945_1,cycle945_2,cycle945_3,cycle945_4,cycle945_5]⟩
lemma valid_data945 : data945.Valid src945 dst945 Finset.univ := by decide +kernel

def src946 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst946 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle946_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle946_1 : CycleData E W := ⟨2,![1,13,21,2],![3,4,28,8]⟩
def cycle946_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle946_3 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle946_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle946_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data946 : PartitionData E W := ⟨6,![cycle946_0,cycle946_1,cycle946_2,cycle946_3,cycle946_4,cycle946_5]⟩
lemma valid_data946 : data946.Valid src946 dst946 Finset.univ := by decide +kernel

def src947 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst947 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle947_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle947_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle947_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle947_3 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle947_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle947_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data947 : PartitionData E W := ⟨6,![cycle947_0,cycle947_1,cycle947_2,cycle947_3,cycle947_4,cycle947_5]⟩
lemma valid_data947 : data947.Valid src947 dst947 Finset.univ := by decide +kernel

def src948 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst948 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle948_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle948_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle948_2 : CycleData E W := ⟨2,![2,3,14,7],![3,8,6,16]⟩
def cycle948_3 : CycleData E W := ⟨2,![4,17,11,5],![2,6,26,14]⟩
def cycle948_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle948_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data948 : PartitionData E W := ⟨6,![cycle948_0,cycle948_1,cycle948_2,cycle948_3,cycle948_4,cycle948_5]⟩
lemma valid_data948 : data948.Valid src948 dst948 Finset.univ := by decide +kernel

def src949 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst949 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle949_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle949_1 : CycleData E W := ⟨2,![1,13,21,2],![3,4,28,8]⟩
def cycle949_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle949_3 : CycleData E W := ⟨3,![6,11,17,14,7],![3,14,26,6,16]⟩
def cycle949_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle949_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data949 : PartitionData E W := ⟨6,![cycle949_0,cycle949_1,cycle949_2,cycle949_3,cycle949_4,cycle949_5]⟩
lemma valid_data949 : data949.Valid src949 dst949 Finset.univ := by decide +kernel

def src950 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst950 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle950_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle950_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle950_2 : CycleData E W := ⟨2,![2,3,14,7],![3,8,6,16]⟩
def cycle950_3 : CycleData E W := ⟨2,![4,17,11,5],![2,6,26,14]⟩
def cycle950_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle950_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data950 : PartitionData E W := ⟨6,![cycle950_0,cycle950_1,cycle950_2,cycle950_3,cycle950_4,cycle950_5]⟩
lemma valid_data950 : data950.Valid src950 dst950 Finset.univ := by decide +kernel

def src951 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst951 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle951_0 : CycleData E W := ⟨2,![0,13,19,9],![2,4,28,18]⟩
def cycle951_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle951_2 : CycleData E W := ⟨2,![2,18,8,7],![3,8,18,16]⟩
def cycle951_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle951_4 : CycleData E W := ⟨2,![4,14,11,5],![2,6,26,14]⟩
def cycle951_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data951 : PartitionData E W := ⟨6,![cycle951_0,cycle951_1,cycle951_2,cycle951_3,cycle951_4,cycle951_5]⟩
lemma valid_data951 : data951.Valid src951 dst951 Finset.univ := by decide +kernel

def src952 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst952 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle952_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle952_1 : CycleData E W := ⟨2,![1,13,21,2],![3,4,28,8]⟩
def cycle952_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle952_3 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle952_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle952_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data952 : PartitionData E W := ⟨6,![cycle952_0,cycle952_1,cycle952_2,cycle952_3,cycle952_4,cycle952_5]⟩
lemma valid_data952 : data952.Valid src952 dst952 Finset.univ := by decide +kernel

def src953 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst953 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle953_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle953_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle953_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle953_3 : CycleData E W := ⟨3,![4,14,12,19,9],![2,6,26,28,18]⟩
def cycle953_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle953_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data953 : PartitionData E W := ⟨6,![cycle953_0,cycle953_1,cycle953_2,cycle953_3,cycle953_4,cycle953_5]⟩
lemma valid_data953 : data953.Valid src953 dst953 Finset.univ := by decide +kernel

def src954 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst954 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle954_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle954_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle954_2 : CycleData E W := ⟨3,![2,18,19,11,6],![3,8,18,28,14]⟩
def cycle954_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle954_4 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle954_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data954 : PartitionData E W := ⟨6,![cycle954_0,cycle954_1,cycle954_2,cycle954_3,cycle954_4,cycle954_5]⟩
lemma valid_data954 : data954.Valid src954 dst954 Finset.univ := by decide +kernel

def src955 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst955 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle955_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle955_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle955_2 : CycleData E W := ⟨2,![2,21,11,6],![3,8,28,14]⟩
def cycle955_3 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle955_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle955_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data955 : PartitionData E W := ⟨6,![cycle955_0,cycle955_1,cycle955_2,cycle955_3,cycle955_4,cycle955_5]⟩
lemma valid_data955 : data955.Valid src955 dst955 Finset.univ := by decide +kernel

def src956 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst956 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle956_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle956_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle956_2 : CycleData E W := ⟨2,![2,18,11,6],![3,8,28,14]⟩
def cycle956_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle956_4 : CycleData E W := ⟨2,![4,14,8,9],![2,6,16,18]⟩
def cycle956_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data956 : PartitionData E W := ⟨6,![cycle956_0,cycle956_1,cycle956_2,cycle956_3,cycle956_4,cycle956_5]⟩
lemma valid_data956 : data956.Valid src956 dst956 Finset.univ := by decide +kernel

def src957 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst957 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle957_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle957_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle957_2 : CycleData E W := ⟨2,![2,3,14,7],![3,8,6,16]⟩
def cycle957_3 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle957_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle957_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data957 : PartitionData E W := ⟨6,![cycle957_0,cycle957_1,cycle957_2,cycle957_3,cycle957_4,cycle957_5]⟩
lemma valid_data957 : data957.Valid src957 dst957 Finset.univ := by decide +kernel

def src958 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst958 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle958_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle958_1 : CycleData E W := ⟨3,![1,13,17,14,7],![3,4,26,6,16]⟩
def cycle958_2 : CycleData E W := ⟨2,![2,21,11,6],![3,8,28,14]⟩
def cycle958_3 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle958_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle958_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data958 : PartitionData E W := ⟨6,![cycle958_0,cycle958_1,cycle958_2,cycle958_3,cycle958_4,cycle958_5]⟩
lemma valid_data958 : data958.Valid src958 dst958 Finset.univ := by decide +kernel

def src959 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst959 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle959_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle959_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle959_2 : CycleData E W := ⟨2,![2,3,14,7],![3,8,6,16]⟩
def cycle959_3 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle959_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle959_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data959 : PartitionData E W := ⟨6,![cycle959_0,cycle959_1,cycle959_2,cycle959_3,cycle959_4,cycle959_5]⟩
lemma valid_data959 : data959.Valid src959 dst959 Finset.univ := by decide +kernel

def src960 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst960 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle960_0 : CycleData E W := ⟨2,![0,13,14,4],![2,4,26,6]⟩
def cycle960_1 : CycleData E W := ⟨1,![1,10,6],![3,4,14]⟩
def cycle960_2 : CycleData E W := ⟨2,![2,18,8,7],![3,8,18,16]⟩
def cycle960_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle960_4 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle960_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data960 : PartitionData E W := ⟨6,![cycle960_0,cycle960_1,cycle960_2,cycle960_3,cycle960_4,cycle960_5]⟩
lemma valid_data960 : data960.Valid src960 dst960 Finset.univ := by decide +kernel

def src961 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst961 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle961_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle961_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle961_2 : CycleData E W := ⟨2,![2,21,11,6],![3,8,28,14]⟩
def cycle961_3 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle961_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle961_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data961 : PartitionData E W := ⟨6,![cycle961_0,cycle961_1,cycle961_2,cycle961_3,cycle961_4,cycle961_5]⟩
lemma valid_data961 : data961.Valid src961 dst961 Finset.univ := by decide +kernel

def src962 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst962 : E → W := ![4,3,8,6,2,14,3,16,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle962_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle962_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle962_2 : CycleData E W := ⟨2,![2,18,11,6],![3,8,28,14]⟩
def cycle962_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle962_4 : CycleData E W := ⟨3,![4,14,12,19,9],![2,6,26,28,18]⟩
def cycle962_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data962 : PartitionData E W := ⟨6,![cycle962_0,cycle962_1,cycle962_2,cycle962_3,cycle962_4,cycle962_5]⟩
lemma valid_data962 : data962.Valid src962 dst962 Finset.univ := by decide +kernel

def src963 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst963 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle963_0 : CycleData E W := ⟨9,![5,12,13,10,16,17,14,7,2,18,9],![2,14,28,4,26,38,6,16,3,8,18]⟩
def cycle963_1 : CycleData E W := ⟨9,![0,1,6,11,15,8,19,20,21,3,4],![2,4,3,14,26,16,18,28,38,8,6]⟩
def data963 : PartitionData E W := ⟨2,![cycle963_0,cycle963_1]⟩
lemma valid_data963 : data963.Valid src963 dst963 Finset.univ := by decide +kernel

def src964 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst964 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle964_0 : CycleData E W := ⟨9,![5,12,13,10,16,17,14,7,2,18,9],![2,14,28,4,26,38,6,16,3,8,18]⟩
def cycle964_1 : CycleData E W := ⟨9,![0,1,6,11,15,8,19,20,21,3,4],![2,4,3,14,26,16,18,38,28,8,6]⟩
def data964 : PartitionData E W := ⟨2,![cycle964_0,cycle964_1]⟩
lemma valid_data964 : data964.Valid src964 dst964 Finset.univ := by decide +kernel

def src965 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst965 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle965_0 : CycleData E W := ⟨9,![5,12,18,3,17,16,10,1,7,8,9],![2,14,28,8,6,38,26,4,3,16,18]⟩
def cycle965_1 : CycleData E W := ⟨9,![0,13,19,20,21,2,6,11,15,14,4],![2,4,28,18,38,8,3,14,26,16,6]⟩
def data965 : PartitionData E W := ⟨2,![cycle965_0,cycle965_1]⟩
lemma valid_data965 : data965.Valid src965 dst965 Finset.univ := by decide +kernel

def src966 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst966 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle966_0 : CycleData E W := ⟨9,![4,14,15,16,10,13,12,6,2,18,9],![2,6,16,38,26,4,28,14,3,8,18]⟩
def cycle966_1 : CycleData E W := ⟨9,![0,1,7,8,19,20,21,3,17,11,5],![2,4,3,16,18,28,38,8,6,26,14]⟩
def data966 : PartitionData E W := ⟨2,![cycle966_0,cycle966_1]⟩
lemma valid_data966 : data966.Valid src966 dst966 Finset.univ := by decide +kernel

def src967 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst967 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle967_0 : CycleData E W := ⟨9,![4,14,15,16,10,13,12,6,2,18,9],![2,6,16,38,26,4,28,14,3,8,18]⟩
def cycle967_1 : CycleData E W := ⟨9,![0,1,7,8,19,20,21,3,17,11,5],![2,4,3,16,18,38,28,8,6,26,14]⟩
def data967 : PartitionData E W := ⟨2,![cycle967_0,cycle967_1]⟩
lemma valid_data967 : data967.Valid src967 dst967 Finset.univ := by decide +kernel

def src968 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst968 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle968_0 : CycleData E W := ⟨9,![4,3,18,12,6,1,10,16,15,8,9],![2,6,8,28,14,3,4,26,38,16,18]⟩
def cycle968_1 : CycleData E W := ⟨9,![0,13,19,20,21,2,7,14,17,11,5],![2,4,28,18,38,8,3,16,6,26,14]⟩
def data968 : PartitionData E W := ⟨2,![cycle968_0,cycle968_1]⟩
lemma valid_data968 : data968.Valid src968 dst968 Finset.univ := by decide +kernel

def src969 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst969 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle969_0 : CycleData E W := ⟨9,![5,12,13,10,14,17,16,7,2,18,9],![2,14,28,4,26,6,38,16,3,8,18]⟩
def cycle969_1 : CycleData E W := ⟨9,![0,1,6,11,15,8,19,20,21,3,4],![2,4,3,14,26,16,18,28,38,8,6]⟩
def data969 : PartitionData E W := ⟨2,![cycle969_0,cycle969_1]⟩
lemma valid_data969 : data969.Valid src969 dst969 Finset.univ := by decide +kernel

def src970 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst970 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle970_0 : CycleData E W := ⟨9,![5,12,13,10,14,17,16,7,2,18,9],![2,14,28,4,26,6,38,16,3,8,18]⟩
def cycle970_1 : CycleData E W := ⟨9,![0,1,6,11,15,8,19,20,21,3,4],![2,4,3,14,26,16,18,38,28,8,6]⟩
def data970 : PartitionData E W := ⟨2,![cycle970_0,cycle970_1]⟩
lemma valid_data970 : data970.Valid src970 dst970 Finset.univ := by decide +kernel

def src971 : E → W := ![2,4,3,8,6,2,14,3,16,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst971 : E → W := ![4,3,8,6,2,14,3,16,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle971_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle971_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle971_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle971_3 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle971_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle971_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data971 : PartitionData E W := ⟨6,![cycle971_0,cycle971_1,cycle971_2,cycle971_3,cycle971_4,cycle971_5]⟩
lemma valid_data971 : data971.Valid src971 dst971 Finset.univ := by decide +kernel

def src972 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst972 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle972_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle972_1 : CycleData E W := ⟨2,![1,13,19,8],![3,4,28,18]⟩
def cycle972_2 : CycleData E W := ⟨2,![2,3,14,7],![3,8,6,16]⟩
def cycle972_3 : CycleData E W := ⟨3,![4,17,21,18,9],![2,6,38,8,18]⟩
def cycle972_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle972_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data972 : PartitionData E W := ⟨6,![cycle972_0,cycle972_1,cycle972_2,cycle972_3,cycle972_4,cycle972_5]⟩
lemma valid_data972 : data972.Valid src972 dst972 Finset.univ := by decide +kernel

def src973 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst973 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle973_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle973_1 : CycleData E W := ⟨2,![1,13,21,2],![3,4,28,8]⟩
def cycle973_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle973_3 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle973_4 : CycleData E W := ⟨3,![7,14,17,19,8],![3,16,6,38,18]⟩
def cycle973_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data973 : PartitionData E W := ⟨6,![cycle973_0,cycle973_1,cycle973_2,cycle973_3,cycle973_4,cycle973_5]⟩
lemma valid_data973 : data973.Valid src973 dst973 Finset.univ := by decide +kernel

def src974 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst974 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle974_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle974_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle974_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle974_3 : CycleData E W := ⟨3,![4,14,7,8,9],![2,6,16,3,18]⟩
def cycle974_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle974_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data974 : PartitionData E W := ⟨6,![cycle974_0,cycle974_1,cycle974_2,cycle974_3,cycle974_4,cycle974_5]⟩
lemma valid_data974 : data974.Valid src974 dst974 Finset.univ := by decide +kernel

def src975 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst975 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle975_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle975_1 : CycleData E W := ⟨2,![1,13,19,8],![3,4,28,18]⟩
def cycle975_2 : CycleData E W := ⟨2,![2,21,15,7],![3,8,38,16]⟩
def cycle975_3 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle975_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle975_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data975 : PartitionData E W := ⟨6,![cycle975_0,cycle975_1,cycle975_2,cycle975_3,cycle975_4,cycle975_5]⟩
lemma valid_data975 : data975.Valid src975 dst975 Finset.univ := by decide +kernel

def src976 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst976 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle976_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle976_1 : CycleData E W := ⟨2,![1,13,21,2],![3,4,28,8]⟩
def cycle976_2 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle976_3 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle976_4 : CycleData E W := ⟨2,![7,15,19,8],![3,16,38,18]⟩
def cycle976_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data976 : PartitionData E W := ⟨6,![cycle976_0,cycle976_1,cycle976_2,cycle976_3,cycle976_4,cycle976_5]⟩
lemma valid_data976 : data976.Valid src976 dst976 Finset.univ := by decide +kernel

def src977 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst977 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle977_0 : CycleData E W := ⟨9,![4,3,18,12,16,15,6,10,1,8,9],![2,6,8,28,26,38,16,14,4,3,18]⟩
def cycle977_1 : CycleData E W := ⟨9,![0,13,19,20,21,2,7,14,17,11,5],![2,4,28,18,38,8,3,16,6,26,14]⟩
def data977 : PartitionData E W := ⟨2,![cycle977_0,cycle977_1]⟩
lemma valid_data977 : data977.Valid src977 dst977 Finset.univ := by decide +kernel

def src978 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst978 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle978_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle978_1 : CycleData E W := ⟨2,![1,13,19,8],![3,4,28,18]⟩
def cycle978_2 : CycleData E W := ⟨2,![2,21,16,7],![3,8,38,16]⟩
def cycle978_3 : CycleData E W := ⟨2,![4,3,18,9],![2,6,8,18]⟩
def cycle978_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle978_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data978 : PartitionData E W := ⟨6,![cycle978_0,cycle978_1,cycle978_2,cycle978_3,cycle978_4,cycle978_5]⟩
lemma valid_data978 : data978.Valid src978 dst978 Finset.univ := by decide +kernel

def src979 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst979 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle979_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle979_1 : CycleData E W := ⟨3,![1,13,20,16,7],![3,4,28,38,16]⟩
def cycle979_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle979_3 : CycleData E W := ⟨2,![3,21,12,14],![6,8,28,26]⟩
def cycle979_4 : CycleData E W := ⟨2,![4,17,19,9],![2,6,38,18]⟩
def cycle979_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data979 : PartitionData E W := ⟨6,![cycle979_0,cycle979_1,cycle979_2,cycle979_3,cycle979_4,cycle979_5]⟩
lemma valid_data979 : data979.Valid src979 dst979 Finset.univ := by decide +kernel

def src980 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst980 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle980_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle980_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle980_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle980_3 : CycleData E W := ⟨3,![4,14,12,19,9],![2,6,26,28,18]⟩
def cycle980_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle980_5 : CycleData E W := ⟨2,![7,16,20,8],![3,16,38,18]⟩
def data980 : PartitionData E W := ⟨6,![cycle980_0,cycle980_1,cycle980_2,cycle980_3,cycle980_4,cycle980_5]⟩
lemma valid_data980 : data980.Valid src980 dst980 Finset.univ := by decide +kernel

def src981 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst981 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle981_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle981_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle981_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle981_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle981_4 : CycleData E W := ⟨4,![4,14,6,11,19,9],![2,6,16,14,28,18]⟩
def cycle981_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data981 : PartitionData E W := ⟨6,![cycle981_0,cycle981_1,cycle981_2,cycle981_3,cycle981_4,cycle981_5]⟩
lemma valid_data981 : data981.Valid src981 dst981 Finset.univ := by decide +kernel

def src982 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst982 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle982_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle982_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle982_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle982_3 : CycleData E W := ⟨3,![3,21,11,6,14],![6,8,28,14,16]⟩
def cycle982_4 : CycleData E W := ⟨2,![4,17,19,9],![2,6,38,18]⟩
def cycle982_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data982 : PartitionData E W := ⟨6,![cycle982_0,cycle982_1,cycle982_2,cycle982_3,cycle982_4,cycle982_5]⟩
lemma valid_data982 : data982.Valid src982 dst982 Finset.univ := by decide +kernel

def src983 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst983 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle983_0 : CycleData E W := ⟨9,![0,13,16,17,3,18,11,6,7,8,9],![2,4,26,38,6,8,28,14,16,3,18]⟩
def cycle983_1 : CycleData E W := ⟨9,![4,14,15,12,19,20,21,2,1,10,5],![2,6,16,26,28,18,38,8,3,4,14]⟩
def data983 : PartitionData E W := ⟨2,![cycle983_0,cycle983_1]⟩
lemma valid_data983 : data983.Valid src983 dst983 Finset.univ := by decide +kernel

def src984 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst984 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle984_0 : CycleData E W := ⟨2,![0,13,17,4],![2,4,26,6]⟩
def cycle984_1 : CycleData E W := ⟨2,![1,10,6,7],![3,4,14,16]⟩
def cycle984_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle984_3 : CycleData E W := ⟨2,![3,21,15,14],![6,8,38,16]⟩
def cycle984_4 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle984_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data984 : PartitionData E W := ⟨6,![cycle984_0,cycle984_1,cycle984_2,cycle984_3,cycle984_4,cycle984_5]⟩
lemma valid_data984 : data984.Valid src984 dst984 Finset.univ := by decide +kernel

def src985 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst985 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle985_0 : CycleData E W := ⟨9,![0,10,11,12,16,15,7,8,18,3,4],![2,4,14,28,26,38,16,3,18,8,6]⟩
def cycle985_1 : CycleData E W := ⟨9,![5,6,14,17,13,1,2,21,20,19,9],![2,14,16,6,26,4,3,8,28,38,18]⟩
def data985 : PartitionData E W := ⟨2,![cycle985_0,cycle985_1]⟩
lemma valid_data985 : data985.Valid src985 dst985 Finset.univ := by decide +kernel

def src986 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst986 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle986_0 : CycleData E W := ⟨9,![4,3,18,12,16,15,6,10,1,8,9],![2,6,8,28,26,38,16,14,4,3,18]⟩
def cycle986_1 : CycleData E W := ⟨9,![0,13,17,14,7,2,21,20,19,11,5],![2,4,26,6,16,3,8,38,18,28,14]⟩
def data986 : PartitionData E W := ⟨2,![cycle986_0,cycle986_1]⟩
lemma valid_data986 : data986.Valid src986 dst986 Finset.univ := by decide +kernel

def src987 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst987 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle987_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle987_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle987_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle987_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle987_4 : CycleData E W := ⟨3,![4,14,12,19,9],![2,6,26,28,18]⟩
def cycle987_5 : CycleData E W := ⟨2,![6,16,20,11],![14,16,38,28]⟩
def data987 : PartitionData E W := ⟨6,![cycle987_0,cycle987_1,cycle987_2,cycle987_3,cycle987_4,cycle987_5]⟩
lemma valid_data987 : data987.Valid src987 dst987 Finset.univ := by decide +kernel

def src988 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst988 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle988_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle988_1 : CycleData E W := ⟨2,![1,13,15,7],![3,4,26,16]⟩
def cycle988_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle988_3 : CycleData E W := ⟨2,![3,21,12,14],![6,8,28,26]⟩
def cycle988_4 : CycleData E W := ⟨2,![4,17,19,9],![2,6,38,18]⟩
def cycle988_5 : CycleData E W := ⟨2,![6,16,20,11],![14,16,38,28]⟩
def data988 : PartitionData E W := ⟨6,![cycle988_0,cycle988_1,cycle988_2,cycle988_3,cycle988_4,cycle988_5]⟩
lemma valid_data988 : data988.Valid src988 dst988 Finset.univ := by decide +kernel

def src989 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst989 : E → W := ![4,3,8,6,2,14,16,3,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle989_0 : CycleData E W := ⟨9,![5,6,16,17,3,18,12,13,1,8,9],![2,14,16,38,6,8,28,26,4,3,18]⟩
def cycle989_1 : CycleData E W := ⟨9,![0,10,11,19,20,21,2,7,15,14,4],![2,4,14,28,18,38,8,3,16,26,6]⟩
def data989 : PartitionData E W := ⟨2,![cycle989_0,cycle989_1]⟩
lemma valid_data989 : data989.Valid src989 dst989 Finset.univ := by decide +kernel

def src990 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst990 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle990_0 : CycleData E W := ⟨3,![0,1,7,14,4],![2,4,3,16,6]⟩
def cycle990_1 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle990_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle990_3 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle990_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle990_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data990 : PartitionData E W := ⟨6,![cycle990_0,cycle990_1,cycle990_2,cycle990_3,cycle990_4,cycle990_5]⟩
lemma valid_data990 : data990.Valid src990 dst990 Finset.univ := by decide +kernel

def src991 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst991 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle991_0 : CycleData E W := ⟨9,![4,17,16,10,13,12,6,7,2,18,9],![2,6,38,26,4,28,14,16,3,8,18]⟩
def cycle991_1 : CycleData E W := ⟨9,![0,1,8,19,20,21,3,14,15,11,5],![2,4,3,18,38,28,8,6,16,26,14]⟩
def data991 : PartitionData E W := ⟨2,![cycle991_0,cycle991_1]⟩
lemma valid_data991 : data991.Valid src991 dst991 Finset.univ := by decide +kernel

def src992 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst992 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle992_0 : CycleData E W := ⟨9,![0,13,18,3,17,16,11,6,7,8,9],![2,4,28,8,6,38,26,14,16,3,18]⟩
def cycle992_1 : CycleData E W := ⟨9,![4,14,15,10,1,2,21,20,19,12,5],![2,6,16,26,4,3,8,38,18,28,14]⟩
def data992 : PartitionData E W := ⟨2,![cycle992_0,cycle992_1]⟩
lemma valid_data992 : data992.Valid src992 dst992 Finset.univ := by decide +kernel

def src993 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst993 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle993_0 : CycleData E W := ⟨9,![0,13,12,11,16,15,7,8,18,3,4],![2,4,28,14,26,38,16,3,18,8,6]⟩
def cycle993_1 : CycleData E W := ⟨9,![5,6,14,17,10,1,2,21,20,19,9],![2,14,16,6,26,4,3,8,38,28,18]⟩
def data993 : PartitionData E W := ⟨2,![cycle993_0,cycle993_1]⟩
lemma valid_data993 : data993.Valid src993 dst993 Finset.univ := by decide +kernel

def src994 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst994 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle994_0 : CycleData E W := ⟨9,![0,13,12,11,16,15,7,8,18,3,4],![2,4,28,14,26,38,16,3,18,8,6]⟩
def cycle994_1 : CycleData E W := ⟨9,![5,6,14,17,10,1,2,21,20,19,9],![2,14,16,6,26,4,3,8,28,38,18]⟩
def data994 : PartitionData E W := ⟨2,![cycle994_0,cycle994_1]⟩
lemma valid_data994 : data994.Valid src994 dst994 Finset.univ := by decide +kernel

def src995 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst995 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle995_0 : CycleData E W := ⟨9,![4,3,18,12,6,15,16,10,1,8,9],![2,6,8,28,14,16,38,26,4,3,18]⟩
def cycle995_1 : CycleData E W := ⟨9,![0,13,19,20,21,2,7,14,17,11,5],![2,4,28,18,38,8,3,16,6,26,14]⟩
def data995 : PartitionData E W := ⟨2,![cycle995_0,cycle995_1]⟩
lemma valid_data995 : data995.Valid src995 dst995 Finset.univ := by decide +kernel

def src996 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst996 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle996_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle996_1 : CycleData E W := ⟨3,![1,13,20,16,7],![3,4,28,38,16]⟩
def cycle996_2 : CycleData E W := ⟨1,![2,18,8],![3,8,18]⟩
def cycle996_3 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle996_4 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle996_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data996 : PartitionData E W := ⟨6,![cycle996_0,cycle996_1,cycle996_2,cycle996_3,cycle996_4,cycle996_5]⟩
lemma valid_data996 : data996.Valid src996 dst996 Finset.univ := by decide +kernel

def src997 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst997 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle997_0 : CycleData E W := ⟨9,![0,13,12,11,14,17,16,7,2,18,9],![2,4,28,14,26,6,38,16,3,8,18]⟩
def cycle997_1 : CycleData E W := ⟨9,![4,3,21,20,19,8,1,10,15,6,5],![2,6,8,28,38,18,3,4,26,16,14]⟩
def data997 : PartitionData E W := ⟨2,![cycle997_0,cycle997_1]⟩
lemma valid_data997 : data997.Valid src997 dst997 Finset.univ := by decide +kernel

def src998 : E → W := ![2,4,3,8,6,2,14,16,3,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst998 : E → W := ![4,3,8,6,2,14,16,3,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle998_0 : CycleData E W := ⟨2,![0,10,14,4],![2,4,26,6]⟩
def cycle998_1 : CycleData E W := ⟨2,![1,13,18,2],![3,4,28,8]⟩
def cycle998_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle998_3 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle998_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle998_5 : CycleData E W := ⟨2,![7,16,20,8],![3,16,38,18]⟩
def data998 : PartitionData E W := ⟨6,![cycle998_0,cycle998_1,cycle998_2,cycle998_3,cycle998_4,cycle998_5]⟩
lemma valid_data998 : data998.Valid src998 dst998 Finset.univ := by decide +kernel

def src999 : E → W := ![2,4,3,8,6,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst999 : E → W := ![4,3,8,6,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle999_0 : CycleData E W := ⟨2,![0,1,8,9],![2,4,3,16]⟩
def cycle999_1 : CycleData E W := ⟨1,![2,18,7],![3,8,18]⟩
def cycle999_2 : CycleData E W := ⟨1,![3,21,17],![6,8,38]⟩
def cycle999_3 : CycleData E W := ⟨3,![4,14,15,11,5],![2,6,16,26,14]⟩
def cycle999_4 : CycleData E W := ⟨2,![10,6,19,13],![4,14,18,28]⟩
def cycle999_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data999 : PartitionData E W := ⟨6,![cycle999_0,cycle999_1,cycle999_2,cycle999_3,cycle999_4,cycle999_5]⟩
lemma valid_data999 : data999.Valid src999 dst999 Finset.univ := by decide +kernel

def lookupB4 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data800 else (if j < 2 then data801 else data802)) else (if j < 4 then data803 else (if j < 5 then data804 else data805))) else (if j < 9 then (if j < 7 then data806 else (if j < 8 then data807 else data808)) else (if j < 10 then data809 else (if j < 11 then data810 else data811)))) else (if j < 18 then (if j < 15 then (if j < 13 then data812 else (if j < 14 then data813 else data814)) else (if j < 16 then data815 else (if j < 17 then data816 else data817))) else (if j < 21 then (if j < 19 then data818 else (if j < 20 then data819 else data820)) else (if j < 23 then (if j < 22 then data821 else data822) else (if j < 24 then data823 else data824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data825 else (if j < 27 then data826 else data827)) else (if j < 29 then data828 else (if j < 30 then data829 else data830))) else (if j < 34 then (if j < 32 then data831 else (if j < 33 then data832 else data833)) else (if j < 35 then data834 else (if j < 36 then data835 else data836)))) else (if j < 43 then (if j < 40 then (if j < 38 then data837 else (if j < 39 then data838 else data839)) else (if j < 41 then data840 else (if j < 42 then data841 else data842))) else (if j < 46 then (if j < 44 then data843 else (if j < 45 then data844 else data845)) else (if j < 48 then (if j < 47 then data846 else data847) else (if j < 49 then data848 else data849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data850 else (if j < 52 then data851 else data852)) else (if j < 54 then data853 else (if j < 55 then data854 else data855))) else (if j < 59 then (if j < 57 then data856 else (if j < 58 then data857 else data858)) else (if j < 60 then data859 else (if j < 61 then data860 else data861)))) else (if j < 68 then (if j < 65 then (if j < 63 then data862 else (if j < 64 then data863 else data864)) else (if j < 66 then data865 else (if j < 67 then data866 else data867))) else (if j < 71 then (if j < 69 then data868 else (if j < 70 then data869 else data870)) else (if j < 73 then (if j < 72 then data871 else data872) else (if j < 74 then data873 else data874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data875 else (if j < 77 then data876 else data877)) else (if j < 79 then data878 else (if j < 80 then data879 else data880))) else (if j < 84 then (if j < 82 then data881 else (if j < 83 then data882 else data883)) else (if j < 85 then data884 else (if j < 86 then data885 else data886)))) else (if j < 93 then (if j < 90 then (if j < 88 then data887 else (if j < 89 then data888 else data889)) else (if j < 91 then data890 else (if j < 92 then data891 else data892))) else (if j < 96 then (if j < 94 then data893 else (if j < 95 then data894 else data895)) else (if j < 98 then (if j < 97 then data896 else data897) else (if j < 99 then data898 else data899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data900 else (if j < 102 then data901 else data902)) else (if j < 104 then data903 else (if j < 105 then data904 else data905))) else (if j < 109 then (if j < 107 then data906 else (if j < 108 then data907 else data908)) else (if j < 110 then data909 else (if j < 111 then data910 else data911)))) else (if j < 118 then (if j < 115 then (if j < 113 then data912 else (if j < 114 then data913 else data914)) else (if j < 116 then data915 else (if j < 117 then data916 else data917))) else (if j < 121 then (if j < 119 then data918 else (if j < 120 then data919 else data920)) else (if j < 123 then (if j < 122 then data921 else data922) else (if j < 124 then data923 else data924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data925 else (if j < 127 then data926 else data927)) else (if j < 129 then data928 else (if j < 130 then data929 else data930))) else (if j < 134 then (if j < 132 then data931 else (if j < 133 then data932 else data933)) else (if j < 135 then data934 else (if j < 136 then data935 else data936)))) else (if j < 143 then (if j < 140 then (if j < 138 then data937 else (if j < 139 then data938 else data939)) else (if j < 141 then data940 else (if j < 142 then data941 else data942))) else (if j < 146 then (if j < 144 then data943 else (if j < 145 then data944 else data945)) else (if j < 148 then (if j < 147 then data946 else data947) else (if j < 149 then data948 else data949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data950 else (if j < 152 then data951 else data952)) else (if j < 154 then data953 else (if j < 155 then data954 else data955))) else (if j < 159 then (if j < 157 then data956 else (if j < 158 then data957 else data958)) else (if j < 160 then data959 else (if j < 161 then data960 else data961)))) else (if j < 168 then (if j < 165 then (if j < 163 then data962 else (if j < 164 then data963 else data964)) else (if j < 166 then data965 else (if j < 167 then data966 else data967))) else (if j < 171 then (if j < 169 then data968 else (if j < 170 then data969 else data970)) else (if j < 173 then (if j < 172 then data971 else data972) else (if j < 174 then data973 else data974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data975 else (if j < 177 then data976 else data977)) else (if j < 179 then data978 else (if j < 180 then data979 else data980))) else (if j < 184 then (if j < 182 then data981 else (if j < 183 then data982 else data983)) else (if j < 185 then data984 else (if j < 186 then data985 else data986)))) else (if j < 193 then (if j < 190 then (if j < 188 then data987 else (if j < 189 then data988 else data989)) else (if j < 191 then data990 else (if j < 192 then data991 else data992))) else (if j < 196 then (if j < 194 then data993 else (if j < 195 then data994 else data995)) else (if j < 198 then (if j < 197 then data996 else data997) else (if j < 199 then data998 else data999))))))))

def srcTableB4 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src800 else (if j < 2 then src801 else src802)) else (if j < 4 then src803 else (if j < 5 then src804 else src805))) else (if j < 9 then (if j < 7 then src806 else (if j < 8 then src807 else src808)) else (if j < 10 then src809 else (if j < 11 then src810 else src811)))) else (if j < 18 then (if j < 15 then (if j < 13 then src812 else (if j < 14 then src813 else src814)) else (if j < 16 then src815 else (if j < 17 then src816 else src817))) else (if j < 21 then (if j < 19 then src818 else (if j < 20 then src819 else src820)) else (if j < 23 then (if j < 22 then src821 else src822) else (if j < 24 then src823 else src824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src825 else (if j < 27 then src826 else src827)) else (if j < 29 then src828 else (if j < 30 then src829 else src830))) else (if j < 34 then (if j < 32 then src831 else (if j < 33 then src832 else src833)) else (if j < 35 then src834 else (if j < 36 then src835 else src836)))) else (if j < 43 then (if j < 40 then (if j < 38 then src837 else (if j < 39 then src838 else src839)) else (if j < 41 then src840 else (if j < 42 then src841 else src842))) else (if j < 46 then (if j < 44 then src843 else (if j < 45 then src844 else src845)) else (if j < 48 then (if j < 47 then src846 else src847) else (if j < 49 then src848 else src849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src850 else (if j < 52 then src851 else src852)) else (if j < 54 then src853 else (if j < 55 then src854 else src855))) else (if j < 59 then (if j < 57 then src856 else (if j < 58 then src857 else src858)) else (if j < 60 then src859 else (if j < 61 then src860 else src861)))) else (if j < 68 then (if j < 65 then (if j < 63 then src862 else (if j < 64 then src863 else src864)) else (if j < 66 then src865 else (if j < 67 then src866 else src867))) else (if j < 71 then (if j < 69 then src868 else (if j < 70 then src869 else src870)) else (if j < 73 then (if j < 72 then src871 else src872) else (if j < 74 then src873 else src874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src875 else (if j < 77 then src876 else src877)) else (if j < 79 then src878 else (if j < 80 then src879 else src880))) else (if j < 84 then (if j < 82 then src881 else (if j < 83 then src882 else src883)) else (if j < 85 then src884 else (if j < 86 then src885 else src886)))) else (if j < 93 then (if j < 90 then (if j < 88 then src887 else (if j < 89 then src888 else src889)) else (if j < 91 then src890 else (if j < 92 then src891 else src892))) else (if j < 96 then (if j < 94 then src893 else (if j < 95 then src894 else src895)) else (if j < 98 then (if j < 97 then src896 else src897) else (if j < 99 then src898 else src899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src900 else (if j < 102 then src901 else src902)) else (if j < 104 then src903 else (if j < 105 then src904 else src905))) else (if j < 109 then (if j < 107 then src906 else (if j < 108 then src907 else src908)) else (if j < 110 then src909 else (if j < 111 then src910 else src911)))) else (if j < 118 then (if j < 115 then (if j < 113 then src912 else (if j < 114 then src913 else src914)) else (if j < 116 then src915 else (if j < 117 then src916 else src917))) else (if j < 121 then (if j < 119 then src918 else (if j < 120 then src919 else src920)) else (if j < 123 then (if j < 122 then src921 else src922) else (if j < 124 then src923 else src924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src925 else (if j < 127 then src926 else src927)) else (if j < 129 then src928 else (if j < 130 then src929 else src930))) else (if j < 134 then (if j < 132 then src931 else (if j < 133 then src932 else src933)) else (if j < 135 then src934 else (if j < 136 then src935 else src936)))) else (if j < 143 then (if j < 140 then (if j < 138 then src937 else (if j < 139 then src938 else src939)) else (if j < 141 then src940 else (if j < 142 then src941 else src942))) else (if j < 146 then (if j < 144 then src943 else (if j < 145 then src944 else src945)) else (if j < 148 then (if j < 147 then src946 else src947) else (if j < 149 then src948 else src949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src950 else (if j < 152 then src951 else src952)) else (if j < 154 then src953 else (if j < 155 then src954 else src955))) else (if j < 159 then (if j < 157 then src956 else (if j < 158 then src957 else src958)) else (if j < 160 then src959 else (if j < 161 then src960 else src961)))) else (if j < 168 then (if j < 165 then (if j < 163 then src962 else (if j < 164 then src963 else src964)) else (if j < 166 then src965 else (if j < 167 then src966 else src967))) else (if j < 171 then (if j < 169 then src968 else (if j < 170 then src969 else src970)) else (if j < 173 then (if j < 172 then src971 else src972) else (if j < 174 then src973 else src974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src975 else (if j < 177 then src976 else src977)) else (if j < 179 then src978 else (if j < 180 then src979 else src980))) else (if j < 184 then (if j < 182 then src981 else (if j < 183 then src982 else src983)) else (if j < 185 then src984 else (if j < 186 then src985 else src986)))) else (if j < 193 then (if j < 190 then (if j < 188 then src987 else (if j < 189 then src988 else src989)) else (if j < 191 then src990 else (if j < 192 then src991 else src992))) else (if j < 196 then (if j < 194 then src993 else (if j < 195 then src994 else src995)) else (if j < 198 then (if j < 197 then src996 else src997) else (if j < 199 then src998 else src999))))))))

def dstTableB4 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst800 else (if j < 2 then dst801 else dst802)) else (if j < 4 then dst803 else (if j < 5 then dst804 else dst805))) else (if j < 9 then (if j < 7 then dst806 else (if j < 8 then dst807 else dst808)) else (if j < 10 then dst809 else (if j < 11 then dst810 else dst811)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst812 else (if j < 14 then dst813 else dst814)) else (if j < 16 then dst815 else (if j < 17 then dst816 else dst817))) else (if j < 21 then (if j < 19 then dst818 else (if j < 20 then dst819 else dst820)) else (if j < 23 then (if j < 22 then dst821 else dst822) else (if j < 24 then dst823 else dst824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst825 else (if j < 27 then dst826 else dst827)) else (if j < 29 then dst828 else (if j < 30 then dst829 else dst830))) else (if j < 34 then (if j < 32 then dst831 else (if j < 33 then dst832 else dst833)) else (if j < 35 then dst834 else (if j < 36 then dst835 else dst836)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst837 else (if j < 39 then dst838 else dst839)) else (if j < 41 then dst840 else (if j < 42 then dst841 else dst842))) else (if j < 46 then (if j < 44 then dst843 else (if j < 45 then dst844 else dst845)) else (if j < 48 then (if j < 47 then dst846 else dst847) else (if j < 49 then dst848 else dst849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst850 else (if j < 52 then dst851 else dst852)) else (if j < 54 then dst853 else (if j < 55 then dst854 else dst855))) else (if j < 59 then (if j < 57 then dst856 else (if j < 58 then dst857 else dst858)) else (if j < 60 then dst859 else (if j < 61 then dst860 else dst861)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst862 else (if j < 64 then dst863 else dst864)) else (if j < 66 then dst865 else (if j < 67 then dst866 else dst867))) else (if j < 71 then (if j < 69 then dst868 else (if j < 70 then dst869 else dst870)) else (if j < 73 then (if j < 72 then dst871 else dst872) else (if j < 74 then dst873 else dst874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst875 else (if j < 77 then dst876 else dst877)) else (if j < 79 then dst878 else (if j < 80 then dst879 else dst880))) else (if j < 84 then (if j < 82 then dst881 else (if j < 83 then dst882 else dst883)) else (if j < 85 then dst884 else (if j < 86 then dst885 else dst886)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst887 else (if j < 89 then dst888 else dst889)) else (if j < 91 then dst890 else (if j < 92 then dst891 else dst892))) else (if j < 96 then (if j < 94 then dst893 else (if j < 95 then dst894 else dst895)) else (if j < 98 then (if j < 97 then dst896 else dst897) else (if j < 99 then dst898 else dst899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst900 else (if j < 102 then dst901 else dst902)) else (if j < 104 then dst903 else (if j < 105 then dst904 else dst905))) else (if j < 109 then (if j < 107 then dst906 else (if j < 108 then dst907 else dst908)) else (if j < 110 then dst909 else (if j < 111 then dst910 else dst911)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst912 else (if j < 114 then dst913 else dst914)) else (if j < 116 then dst915 else (if j < 117 then dst916 else dst917))) else (if j < 121 then (if j < 119 then dst918 else (if j < 120 then dst919 else dst920)) else (if j < 123 then (if j < 122 then dst921 else dst922) else (if j < 124 then dst923 else dst924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst925 else (if j < 127 then dst926 else dst927)) else (if j < 129 then dst928 else (if j < 130 then dst929 else dst930))) else (if j < 134 then (if j < 132 then dst931 else (if j < 133 then dst932 else dst933)) else (if j < 135 then dst934 else (if j < 136 then dst935 else dst936)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst937 else (if j < 139 then dst938 else dst939)) else (if j < 141 then dst940 else (if j < 142 then dst941 else dst942))) else (if j < 146 then (if j < 144 then dst943 else (if j < 145 then dst944 else dst945)) else (if j < 148 then (if j < 147 then dst946 else dst947) else (if j < 149 then dst948 else dst949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst950 else (if j < 152 then dst951 else dst952)) else (if j < 154 then dst953 else (if j < 155 then dst954 else dst955))) else (if j < 159 then (if j < 157 then dst956 else (if j < 158 then dst957 else dst958)) else (if j < 160 then dst959 else (if j < 161 then dst960 else dst961)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst962 else (if j < 164 then dst963 else dst964)) else (if j < 166 then dst965 else (if j < 167 then dst966 else dst967))) else (if j < 171 then (if j < 169 then dst968 else (if j < 170 then dst969 else dst970)) else (if j < 173 then (if j < 172 then dst971 else dst972) else (if j < 174 then dst973 else dst974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst975 else (if j < 177 then dst976 else dst977)) else (if j < 179 then dst978 else (if j < 180 then dst979 else dst980))) else (if j < 184 then (if j < 182 then dst981 else (if j < 183 then dst982 else dst983)) else (if j < 185 then dst984 else (if j < 186 then dst985 else dst986)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst987 else (if j < 189 then dst988 else dst989)) else (if j < 191 then dst990 else (if j < 192 then dst991 else dst992))) else (if j < 196 then (if j < 194 then dst993 else (if j < 195 then dst994 else dst995)) else (if j < 198 then (if j < 197 then dst996 else dst997) else (if j < 199 then dst998 else dst999))))))))

def caseB4 (i : Fin 200) : Cases := ⟨800 + i.val,by have := i.isLt; omega⟩
lemma tableB4_valid (i : Fin 200) :
    (lookupB4 i.val).Valid (srcTableB4 i.val) (dstTableB4 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data800
  · exact valid_data801
  · exact valid_data802
  · exact valid_data803
  · exact valid_data804
  · exact valid_data805
  · exact valid_data806
  · exact valid_data807
  · exact valid_data808
  · exact valid_data809
  · exact valid_data810
  · exact valid_data811
  · exact valid_data812
  · exact valid_data813
  · exact valid_data814
  · exact valid_data815
  · exact valid_data816
  · exact valid_data817
  · exact valid_data818
  · exact valid_data819
  · exact valid_data820
  · exact valid_data821
  · exact valid_data822
  · exact valid_data823
  · exact valid_data824
  · exact valid_data825
  · exact valid_data826
  · exact valid_data827
  · exact valid_data828
  · exact valid_data829
  · exact valid_data830
  · exact valid_data831
  · exact valid_data832
  · exact valid_data833
  · exact valid_data834
  · exact valid_data835
  · exact valid_data836
  · exact valid_data837
  · exact valid_data838
  · exact valid_data839
  · exact valid_data840
  · exact valid_data841
  · exact valid_data842
  · exact valid_data843
  · exact valid_data844
  · exact valid_data845
  · exact valid_data846
  · exact valid_data847
  · exact valid_data848
  · exact valid_data849
  · exact valid_data850
  · exact valid_data851
  · exact valid_data852
  · exact valid_data853
  · exact valid_data854
  · exact valid_data855
  · exact valid_data856
  · exact valid_data857
  · exact valid_data858
  · exact valid_data859
  · exact valid_data860
  · exact valid_data861
  · exact valid_data862
  · exact valid_data863
  · exact valid_data864
  · exact valid_data865
  · exact valid_data866
  · exact valid_data867
  · exact valid_data868
  · exact valid_data869
  · exact valid_data870
  · exact valid_data871
  · exact valid_data872
  · exact valid_data873
  · exact valid_data874
  · exact valid_data875
  · exact valid_data876
  · exact valid_data877
  · exact valid_data878
  · exact valid_data879
  · exact valid_data880
  · exact valid_data881
  · exact valid_data882
  · exact valid_data883
  · exact valid_data884
  · exact valid_data885
  · exact valid_data886
  · exact valid_data887
  · exact valid_data888
  · exact valid_data889
  · exact valid_data890
  · exact valid_data891
  · exact valid_data892
  · exact valid_data893
  · exact valid_data894
  · exact valid_data895
  · exact valid_data896
  · exact valid_data897
  · exact valid_data898
  · exact valid_data899
  · exact valid_data900
  · exact valid_data901
  · exact valid_data902
  · exact valid_data903
  · exact valid_data904
  · exact valid_data905
  · exact valid_data906
  · exact valid_data907
  · exact valid_data908
  · exact valid_data909
  · exact valid_data910
  · exact valid_data911
  · exact valid_data912
  · exact valid_data913
  · exact valid_data914
  · exact valid_data915
  · exact valid_data916
  · exact valid_data917
  · exact valid_data918
  · exact valid_data919
  · exact valid_data920
  · exact valid_data921
  · exact valid_data922
  · exact valid_data923
  · exact valid_data924
  · exact valid_data925
  · exact valid_data926
  · exact valid_data927
  · exact valid_data928
  · exact valid_data929
  · exact valid_data930
  · exact valid_data931
  · exact valid_data932
  · exact valid_data933
  · exact valid_data934
  · exact valid_data935
  · exact valid_data936
  · exact valid_data937
  · exact valid_data938
  · exact valid_data939
  · exact valid_data940
  · exact valid_data941
  · exact valid_data942
  · exact valid_data943
  · exact valid_data944
  · exact valid_data945
  · exact valid_data946
  · exact valid_data947
  · exact valid_data948
  · exact valid_data949
  · exact valid_data950
  · exact valid_data951
  · exact valid_data952
  · exact valid_data953
  · exact valid_data954
  · exact valid_data955
  · exact valid_data956
  · exact valid_data957
  · exact valid_data958
  · exact valid_data959
  · exact valid_data960
  · exact valid_data961
  · exact valid_data962
  · exact valid_data963
  · exact valid_data964
  · exact valid_data965
  · exact valid_data966
  · exact valid_data967
  · exact valid_data968
  · exact valid_data969
  · exact valid_data970
  · exact valid_data971
  · exact valid_data972
  · exact valid_data973
  · exact valid_data974
  · exact valid_data975
  · exact valid_data976
  · exact valid_data977
  · exact valid_data978
  · exact valid_data979
  · exact valid_data980
  · exact valid_data981
  · exact valid_data982
  · exact valid_data983
  · exact valid_data984
  · exact valid_data985
  · exact valid_data986
  · exact valid_data987
  · exact valid_data988
  · exact valid_data989
  · exact valid_data990
  · exact valid_data991
  · exact valid_data992
  · exact valid_data993
  · exact valid_data994
  · exact valid_data995
  · exact valid_data996
  · exact valid_data997
  · exact valid_data998
  · exact valid_data999

lemma srcB4_row : ∀ (i : Fin 200) (e : E),
    srcTableB4 i.val e = caseSource (caseB4 i) e := by decide +kernel

lemma dstB4_row : ∀ (i : Fin 200) (e : E),
    dstTableB4 i.val e = caseTarget (caseB4 i) e := by decide +kernel

lemma sizeB4 : ∀ i : Fin 200, (lookupB4 i.val).size ≤ 5 →
    (lookupB4 i.val).size = 2 ∧
      (⟨caseKey (caseB4 i),caseKey_lt (caseB4 i)⟩ : Fin 3888) ∈ good := by decide +kernel
lemma certificateB4 (i : Fin 200) : Certificate (caseB4 i) := by
  refine ⟨lookupB4 i.val,?_,sizeB4 i⟩
  have hv := tableB4_valid i
  rw [funext (srcB4_row i),funext (dstB4_row i)] at hv
  exact hv
lemma certificateInterval4 : FiniteIntervals.Covers CertificateAt 800 1000 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 800 200 (fun i _ => certificateB4 i)
#print axioms certificateInterval4
end Erdos184Work.FiveRows1

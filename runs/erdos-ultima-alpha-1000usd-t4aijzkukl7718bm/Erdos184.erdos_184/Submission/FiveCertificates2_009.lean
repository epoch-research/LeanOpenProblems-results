import Submission.FiveCertificates2Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows2
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src1800 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,16,26,38,8,18,28,38]
def dst1800 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1800_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,3]⟩
def cycle1800_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1800_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1800_3 : CycleData E W := ⟨3,![5,4,12,13,10],![2,8,5,26,14]⟩
def cycle1800_4 : CycleData E W := ⟨3,![20,8,17,18,23],![8,18,16,26,38]⟩
def cycle1800_5 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def data1800 : PartitionData E W := ⟨6,![cycle1800_0,cycle1800_1,cycle1800_2,cycle1800_3,cycle1800_4,cycle1800_5]⟩
lemma valid_data1800 : data1800.Valid src1800 dst1800 Finset.univ := by decide +kernel

def src1801 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,16,26,38,8,18,38,28]
def dst1801 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1801_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1801_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1801_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1801_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1801_4 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1801_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1801 : PartitionData E W := ⟨6,![cycle1801_0,cycle1801_1,cycle1801_2,cycle1801_3,cycle1801_4,cycle1801_5]⟩
lemma valid_data1801 : data1801.Valid src1801 dst1801 Finset.univ := by decide +kernel

def src1802 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,16,26,38,8,28,18,38]
def dst1802 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1802_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1802_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1802_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle1802_3 : CycleData E W := ⟨3,![5,23,18,13,10],![2,8,38,26,14]⟩
def cycle1802_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1802_5 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def data1802 : PartitionData E W := ⟨6,![cycle1802_0,cycle1802_1,cycle1802_2,cycle1802_3,cycle1802_4,cycle1802_5]⟩
lemma valid_data1802 : data1802.Valid src1802 dst1802 Finset.univ := by decide +kernel

def src1803 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,16,38,26,8,18,28,38]
def dst1803 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1803_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,3]⟩
def cycle1803_1 : CycleData E W := ⟨3,![1,19,13,14,15],![4,6,26,14,28]⟩
def cycle1803_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1803_3 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1803_4 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1803_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data1803 : PartitionData E W := ⟨6,![cycle1803_0,cycle1803_1,cycle1803_2,cycle1803_3,cycle1803_4,cycle1803_5]⟩
lemma valid_data1803 : data1803.Valid src1803 dst1803 Finset.univ := by decide +kernel

def src1804 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,16,38,26,8,18,38,28]
def dst1804 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1804_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1804_1 : CycleData E W := ⟨3,![3,12,19,16,7],![3,5,26,6,16]⟩
def cycle1804_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1804_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1804_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1804_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1804 : PartitionData E W := ⟨6,![cycle1804_0,cycle1804_1,cycle1804_2,cycle1804_3,cycle1804_4,cycle1804_5]⟩
lemma valid_data1804 : data1804.Valid src1804 dst1804 Finset.univ := by decide +kernel

def src1805 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,16,38,26,8,28,18,38]
def dst1805 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1805_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1805_1 : CycleData E W := ⟨3,![3,12,19,16,7],![3,5,26,6,16]⟩
def cycle1805_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle1805_3 : CycleData E W := ⟨3,![5,23,18,13,10],![2,8,38,26,14]⟩
def cycle1805_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1805_5 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def data1805 : PartitionData E W := ⟨6,![cycle1805_0,cycle1805_1,cycle1805_2,cycle1805_3,cycle1805_4,cycle1805_5]⟩
lemma valid_data1805 : data1805.Valid src1805 dst1805 Finset.univ := by decide +kernel

def src1806 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,26,16,38,8,18,28,38]
def dst1806 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1806_0 : CycleData E W := ⟨3,![0,16,12,4,5],![2,6,26,5,8]⟩
def cycle1806_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1806_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1806_3 : CycleData E W := ⟨3,![6,7,17,13,10],![2,3,16,26,14]⟩
def cycle1806_4 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1806_5 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def data1806 : PartitionData E W := ⟨6,![cycle1806_0,cycle1806_1,cycle1806_2,cycle1806_3,cycle1806_4,cycle1806_5]⟩
lemma valid_data1806 : data1806.Valid src1806 dst1806 Finset.univ := by decide +kernel

def src1807 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,26,16,38,8,18,38,28]
def dst1807 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1807_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1807_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1807_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1807_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1807_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1807_5 : CycleData E W := ⟨3,![16,13,14,22,19],![6,26,14,28,38]⟩
def data1807 : PartitionData E W := ⟨6,![cycle1807_0,cycle1807_1,cycle1807_2,cycle1807_3,cycle1807_4,cycle1807_5]⟩
lemma valid_data1807 : data1807.Valid src1807 dst1807 Finset.univ := by decide +kernel

def src1808 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,5,26,14,28,6,26,16,38,8,28,18,38]
def dst1808 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,5,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1808_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1808_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1808_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle1808_3 : CycleData E W := ⟨4,![5,23,19,16,13,10],![2,8,38,6,26,14]⟩
def cycle1808_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1808_5 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def data1808 : PartitionData E W := ⟨6,![cycle1808_0,cycle1808_1,cycle1808_2,cycle1808_3,cycle1808_4,cycle1808_5]⟩
lemma valid_data1808 : data1808.Valid src1808 dst1808 Finset.univ := by decide +kernel

def src1809 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,16,26,38,8,18,28,38]
def dst1809 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,16,26,38,6,18,28,38,8]
def cycle1809_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1809_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1809_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1809_3 : CycleData E W := ⟨3,![16,8,20,23,19],![6,16,18,8,38]⟩
def cycle1809_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle1809_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1809 : PartitionData E W := ⟨6,![cycle1809_0,cycle1809_1,cycle1809_2,cycle1809_3,cycle1809_4,cycle1809_5]⟩
lemma valid_data1809 : data1809.Valid src1809 dst1809 Finset.univ := by decide +kernel

def src1810 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,16,26,38,8,18,38,28]
def dst1810 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,16,26,38,6,18,38,28,8]
def cycle1810_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1810_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1810_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1810_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1810_4 : CycleData E W := ⟨3,![11,9,20,23,15],![4,14,18,8,28]⟩
def cycle1810_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1810 : PartitionData E W := ⟨6,![cycle1810_0,cycle1810_1,cycle1810_2,cycle1810_3,cycle1810_4,cycle1810_5]⟩
lemma valid_data1810 : data1810.Valid src1810 dst1810 Finset.univ := by decide +kernel

def src1811 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,16,26,38,8,28,18,38]
def dst1811 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,16,26,38,6,28,18,38,8]
def cycle1811_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1811_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1811_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1811_3 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1811_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle1811_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1811 : PartitionData E W := ⟨6,![cycle1811_0,cycle1811_1,cycle1811_2,cycle1811_3,cycle1811_4,cycle1811_5]⟩
lemma valid_data1811 : data1811.Valid src1811 dst1811 Finset.univ := by decide +kernel

def src1812 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,16,38,26,8,18,28,38]
def dst1812 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,16,38,26,6,18,28,38,8]
def cycle1812_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1812_1 : CycleData E W := ⟨3,![3,13,19,16,7],![3,5,26,6,16]⟩
def cycle1812_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1812_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle1812_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle1812_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1812 : PartitionData E W := ⟨6,![cycle1812_0,cycle1812_1,cycle1812_2,cycle1812_3,cycle1812_4,cycle1812_5]⟩
lemma valid_data1812 : data1812.Valid src1812 dst1812 Finset.univ := by decide +kernel

def src1813 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,16,38,26,8,18,38,28]
def dst1813 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,16,38,26,6,18,38,28,8]
def cycle1813_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1813_1 : CycleData E W := ⟨3,![3,13,19,16,7],![3,5,26,6,16]⟩
def cycle1813_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1813_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1813_4 : CycleData E W := ⟨3,![11,9,20,23,15],![4,14,18,8,28]⟩
def cycle1813_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1813 : PartitionData E W := ⟨6,![cycle1813_0,cycle1813_1,cycle1813_2,cycle1813_3,cycle1813_4,cycle1813_5]⟩
lemma valid_data1813 : data1813.Valid src1813 dst1813 Finset.univ := by decide +kernel

def src1814 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,16,38,26,8,28,18,38]
def dst1814 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,16,38,26,6,28,18,38,8]
def cycle1814_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1814_1 : CycleData E W := ⟨3,![3,13,19,16,7],![3,5,26,6,16]⟩
def cycle1814_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1814_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1814_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle1814_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1814 : PartitionData E W := ⟨6,![cycle1814_0,cycle1814_1,cycle1814_2,cycle1814_3,cycle1814_4,cycle1814_5]⟩
lemma valid_data1814 : data1814.Valid src1814 dst1814 Finset.univ := by decide +kernel

def src1815 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,26,16,38,8,18,28,38]
def dst1815 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,26,16,38,6,18,28,38,8]
def cycle1815_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1815_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1815_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1815_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1815_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle1815_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1815 : PartitionData E W := ⟨6,![cycle1815_0,cycle1815_1,cycle1815_2,cycle1815_3,cycle1815_4,cycle1815_5]⟩
lemma valid_data1815 : data1815.Valid src1815 dst1815 Finset.univ := by decide +kernel

def src1816 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,26,16,38,8,18,38,28]
def dst1816 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,26,16,38,6,18,38,28,8]
def cycle1816_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1816_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1816_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1816_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1816_4 : CycleData E W := ⟨3,![11,9,20,23,15],![4,14,18,8,28]⟩
def cycle1816_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1816 : PartitionData E W := ⟨6,![cycle1816_0,cycle1816_1,cycle1816_2,cycle1816_3,cycle1816_4,cycle1816_5]⟩
lemma valid_data1816 : data1816.Valid src1816 dst1816 Finset.univ := by decide +kernel

def src1817 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,5,26,28,6,26,16,38,8,28,18,38]
def dst1817 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,5,26,28,4,26,16,38,6,28,18,38,8]
def cycle1817_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1817_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1817_2 : CycleData E W := ⟨2,![5,4,12,10],![2,8,5,14]⟩
def cycle1817_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1817_4 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def cycle1817_5 : CycleData E W := ⟨3,![16,14,20,23,19],![6,26,28,8,38]⟩
def data1817 : PartitionData E W := ⟨6,![cycle1817_0,cycle1817_1,cycle1817_2,cycle1817_3,cycle1817_4,cycle1817_5]⟩
lemma valid_data1817 : data1817.Valid src1817 dst1817 Finset.univ := by decide +kernel

def src1818 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,16,26,38,8,18,28,38]
def dst1818 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,16,26,38,6,18,28,38,8]
def cycle1818_0 : CycleData E W := ⟨10,![5,20,8,7,3,14,15,1,19,18,12,10],![2,8,18,16,3,5,28,4,6,38,26,14]⟩
def cycle1818_1 : CycleData E W := ⟨10,![0,16,17,13,4,23,22,21,9,11,2,6],![2,6,16,26,5,8,38,28,18,14,4,3]⟩
def data1818 : PartitionData E W := ⟨2,![cycle1818_0,cycle1818_1]⟩
lemma valid_data1818 : data1818.Valid src1818 dst1818 Finset.univ := by decide +kernel

def src1819 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,16,26,38,8,18,38,28]
def dst1819 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,16,26,38,6,18,38,28,8]
def cycle1819_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1819_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1819_2 : CycleData E W := ⟨1,![4,23,14],![5,8,28]⟩
def cycle1819_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1819_4 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1819_5 : CycleData E W := ⟨3,![11,12,18,22,15],![4,14,26,38,28]⟩
def data1819 : PartitionData E W := ⟨6,![cycle1819_0,cycle1819_1,cycle1819_2,cycle1819_3,cycle1819_4,cycle1819_5]⟩
lemma valid_data1819 : data1819.Valid src1819 dst1819 Finset.univ := by decide +kernel

def src1820 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,16,26,38,8,28,18,38]
def dst1820 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,16,26,38,6,28,18,38,8]
def cycle1820_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1820_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1820_2 : CycleData E W := ⟨1,![4,20,14],![5,8,28]⟩
def cycle1820_3 : CycleData E W := ⟨3,![5,23,18,12,10],![2,8,38,26,14]⟩
def cycle1820_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1820_5 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def data1820 : PartitionData E W := ⟨6,![cycle1820_0,cycle1820_1,cycle1820_2,cycle1820_3,cycle1820_4,cycle1820_5]⟩
lemma valid_data1820 : data1820.Valid src1820 dst1820 Finset.univ := by decide +kernel

def src1821 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,16,38,26,8,18,28,38]
def dst1821 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,16,38,26,6,18,28,38,8]
def cycle1821_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,3]⟩
def cycle1821_1 : CycleData E W := ⟨2,![1,19,12,11],![4,6,26,14]⟩
def cycle1821_2 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle1821_3 : CycleData E W := ⟨2,![4,23,18,13],![5,8,38,26]⟩
def cycle1821_4 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1821_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data1821 : PartitionData E W := ⟨6,![cycle1821_0,cycle1821_1,cycle1821_2,cycle1821_3,cycle1821_4,cycle1821_5]⟩
lemma valid_data1821 : data1821.Valid src1821 dst1821 Finset.univ := by decide +kernel

def src1822 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,16,38,26,8,18,38,28]
def dst1822 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,16,38,26,6,18,38,28,8]
def cycle1822_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1822_1 : CycleData E W := ⟨3,![3,13,19,16,7],![3,5,26,6,16]⟩
def cycle1822_2 : CycleData E W := ⟨1,![4,23,14],![5,8,28]⟩
def cycle1822_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1822_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1822_5 : CycleData E W := ⟨3,![11,12,18,22,15],![4,14,26,38,28]⟩
def data1822 : PartitionData E W := ⟨6,![cycle1822_0,cycle1822_1,cycle1822_2,cycle1822_3,cycle1822_4,cycle1822_5]⟩
lemma valid_data1822 : data1822.Valid src1822 dst1822 Finset.univ := by decide +kernel

def src1823 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,16,38,26,8,28,18,38]
def dst1823 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,16,38,26,6,28,18,38,8]
def cycle1823_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1823_1 : CycleData E W := ⟨3,![3,13,19,16,7],![3,5,26,6,16]⟩
def cycle1823_2 : CycleData E W := ⟨1,![4,20,14],![5,8,28]⟩
def cycle1823_3 : CycleData E W := ⟨3,![5,23,18,12,10],![2,8,38,26,14]⟩
def cycle1823_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1823_5 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def data1823 : PartitionData E W := ⟨6,![cycle1823_0,cycle1823_1,cycle1823_2,cycle1823_3,cycle1823_4,cycle1823_5]⟩
lemma valid_data1823 : data1823.Valid src1823 dst1823 Finset.univ := by decide +kernel

def src1824 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,26,16,38,8,18,28,38]
def dst1824 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,26,16,38,6,18,28,38,8]
def cycle1824_0 : CycleData E W := ⟨10,![0,19,18,7,2,15,14,13,12,9,20,5],![2,6,38,16,3,4,28,5,26,14,18,8]⟩
def cycle1824_1 : CycleData E W := ⟨10,![6,3,4,23,22,21,8,17,16,1,11,10],![2,3,5,8,38,28,18,16,26,6,4,14]⟩
def data1824 : PartitionData E W := ⟨2,![cycle1824_0,cycle1824_1]⟩
lemma valid_data1824 : data1824.Valid src1824 dst1824 Finset.univ := by decide +kernel

def src1825 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,26,16,38,8,18,38,28]
def dst1825 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,26,16,38,6,18,38,28,8]
def cycle1825_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1825_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1825_2 : CycleData E W := ⟨1,![4,23,14],![5,8,28]⟩
def cycle1825_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1825_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1825_5 : CycleData E W := ⟨4,![11,12,16,19,22,15],![4,14,26,6,38,28]⟩
def data1825 : PartitionData E W := ⟨6,![cycle1825_0,cycle1825_1,cycle1825_2,cycle1825_3,cycle1825_4,cycle1825_5]⟩
lemma valid_data1825 : data1825.Valid src1825 dst1825 Finset.univ := by decide +kernel

def src1826 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,14,26,5,28,6,26,16,38,8,28,18,38]
def dst1826 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,14,26,5,28,4,26,16,38,6,28,18,38,8]
def cycle1826_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1826_1 : CycleData E W := ⟨2,![3,13,17,7],![3,5,26,16]⟩
def cycle1826_2 : CycleData E W := ⟨1,![4,20,14],![5,8,28]⟩
def cycle1826_3 : CycleData E W := ⟨4,![5,23,19,16,12,10],![2,8,38,6,26,14]⟩
def cycle1826_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1826_5 : CycleData E W := ⟨2,![11,9,21,15],![4,14,18,28]⟩
def data1826 : PartitionData E W := ⟨6,![cycle1826_0,cycle1826_1,cycle1826_2,cycle1826_3,cycle1826_4,cycle1826_5]⟩
lemma valid_data1826 : data1826.Valid src1826 dst1826 Finset.univ := by decide +kernel

def src1827 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst1827 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle1827_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1827_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1827_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1827_3 : CycleData E W := ⟨3,![16,8,20,23,19],![6,16,18,8,38]⟩
def cycle1827_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle1827_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1827 : PartitionData E W := ⟨6,![cycle1827_0,cycle1827_1,cycle1827_2,cycle1827_3,cycle1827_4,cycle1827_5]⟩
lemma valid_data1827 : data1827.Valid src1827 dst1827 Finset.univ := by decide +kernel

def src1828 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst1828 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle1828_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1828_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1828_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1828_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1828_4 : CycleData E W := ⟨2,![20,9,14,23],![8,18,14,28]⟩
def cycle1828_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1828 : PartitionData E W := ⟨6,![cycle1828_0,cycle1828_1,cycle1828_2,cycle1828_3,cycle1828_4,cycle1828_5]⟩
lemma valid_data1828 : data1828.Valid src1828 dst1828 Finset.univ := by decide +kernel

def src1829 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,16,26,38,8,28,18,38]
def dst1829 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,16,26,38,6,28,18,38,8]
def cycle1829_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1829_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1829_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1829_3 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1829_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle1829_5 : CycleData E W := ⟨3,![11,18,23,20,15],![4,26,38,8,28]⟩
def data1829 : PartitionData E W := ⟨6,![cycle1829_0,cycle1829_1,cycle1829_2,cycle1829_3,cycle1829_4,cycle1829_5]⟩
lemma valid_data1829 : data1829.Valid src1829 dst1829 Finset.univ := by decide +kernel

def src1830 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,16,38,26,8,18,28,38]
def dst1830 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,16,38,26,6,18,28,38,8]
def cycle1830_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1830_1 : CycleData E W := ⟨3,![3,12,19,16,7],![3,5,26,6,16]⟩
def cycle1830_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1830_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle1830_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle1830_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1830 : PartitionData E W := ⟨6,![cycle1830_0,cycle1830_1,cycle1830_2,cycle1830_3,cycle1830_4,cycle1830_5]⟩
lemma valid_data1830 : data1830.Valid src1830 dst1830 Finset.univ := by decide +kernel

def src1831 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,16,38,26,8,18,38,28]
def dst1831 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,16,38,26,6,18,38,28,8]
def cycle1831_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1831_1 : CycleData E W := ⟨3,![3,12,19,16,7],![3,5,26,6,16]⟩
def cycle1831_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1831_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1831_4 : CycleData E W := ⟨2,![20,9,14,23],![8,18,14,28]⟩
def cycle1831_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1831 : PartitionData E W := ⟨6,![cycle1831_0,cycle1831_1,cycle1831_2,cycle1831_3,cycle1831_4,cycle1831_5]⟩
lemma valid_data1831 : data1831.Valid src1831 dst1831 Finset.univ := by decide +kernel

def src1832 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,16,38,26,8,28,18,38]
def dst1832 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,16,38,26,6,28,18,38,8]
def cycle1832_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1832_1 : CycleData E W := ⟨3,![3,12,19,16,7],![3,5,26,6,16]⟩
def cycle1832_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1832_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1832_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle1832_5 : CycleData E W := ⟨3,![11,18,23,20,15],![4,26,38,8,28]⟩
def data1832 : PartitionData E W := ⟨6,![cycle1832_0,cycle1832_1,cycle1832_2,cycle1832_3,cycle1832_4,cycle1832_5]⟩
lemma valid_data1832 : data1832.Valid src1832 dst1832 Finset.univ := by decide +kernel

def src1833 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,26,16,38,8,18,28,38]
def dst1833 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,26,16,38,6,18,28,38,8]
def cycle1833_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1833_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1833_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1833_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1833_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle1833_5 : CycleData E W := ⟨3,![11,16,19,22,15],![4,26,6,38,28]⟩
def data1833 : PartitionData E W := ⟨6,![cycle1833_0,cycle1833_1,cycle1833_2,cycle1833_3,cycle1833_4,cycle1833_5]⟩
lemma valid_data1833 : data1833.Valid src1833 dst1833 Finset.univ := by decide +kernel

def src1834 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,26,16,38,8,18,38,28]
def dst1834 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,26,16,38,6,18,38,28,8]
def cycle1834_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1834_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1834_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1834_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1834_4 : CycleData E W := ⟨2,![20,9,14,23],![8,18,14,28]⟩
def cycle1834_5 : CycleData E W := ⟨3,![11,16,19,22,15],![4,26,6,38,28]⟩
def data1834 : PartitionData E W := ⟨6,![cycle1834_0,cycle1834_1,cycle1834_2,cycle1834_3,cycle1834_4,cycle1834_5]⟩
lemma valid_data1834 : data1834.Valid src1834 dst1834 Finset.univ := by decide +kernel

def src1835 : E → W := ![2,6,4,3,5,8,2,3,16,18,14,4,26,5,14,28,6,26,16,38,8,28,18,38]
def dst1835 : E → W := ![6,4,3,5,8,2,3,16,18,14,2,26,5,14,28,4,26,16,38,6,28,18,38,8]
def cycle1835_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1835_1 : CycleData E W := ⟨2,![3,12,17,7],![3,5,26,16]⟩
def cycle1835_2 : CycleData E W := ⟨2,![5,4,13,10],![2,8,5,14]⟩
def cycle1835_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1835_4 : CycleData E W := ⟨1,![9,21,14],![14,18,28]⟩
def cycle1835_5 : CycleData E W := ⟨4,![11,16,19,23,20,15],![4,26,6,38,8,28]⟩
def data1835 : PartitionData E W := ⟨6,![cycle1835_0,cycle1835_1,cycle1835_2,cycle1835_3,cycle1835_4,cycle1835_5]⟩
lemma valid_data1835 : data1835.Valid src1835 dst1835 Finset.univ := by decide +kernel

def src1836 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,16,26,38,8,18,28,38]
def dst1836 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1836_0 : CycleData E W := ⟨3,![0,1,15,14,10],![2,6,4,28,14]⟩
def cycle1836_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1836_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1836_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1836_4 : CycleData E W := ⟨3,![16,8,21,22,19],![6,16,18,28,38]⟩
def cycle1836_5 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def data1836 : PartitionData E W := ⟨6,![cycle1836_0,cycle1836_1,cycle1836_2,cycle1836_3,cycle1836_4,cycle1836_5]⟩
lemma valid_data1836 : data1836.Valid src1836 dst1836 Finset.univ := by decide +kernel

def src1837 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,16,26,38,8,18,38,28]
def dst1837 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1837_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1837_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1837_2 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle1837_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1837_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle1837_5 : CycleData E W := ⟨3,![11,12,18,22,15],![4,5,26,38,28]⟩
def data1837 : PartitionData E W := ⟨6,![cycle1837_0,cycle1837_1,cycle1837_2,cycle1837_3,cycle1837_4,cycle1837_5]⟩
lemma valid_data1837 : data1837.Valid src1837 dst1837 Finset.univ := by decide +kernel

def src1838 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,16,26,38,8,28,18,38]
def dst1838 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1838_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1838_1 : CycleData E W := ⟨3,![3,11,15,21,7],![3,5,4,28,18]⟩
def cycle1838_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1838_3 : CycleData E W := ⟨2,![5,20,14,10],![2,8,28,14]⟩
def cycle1838_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1838_5 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def data1838 : PartitionData E W := ⟨6,![cycle1838_0,cycle1838_1,cycle1838_2,cycle1838_3,cycle1838_4,cycle1838_5]⟩
lemma valid_data1838 : data1838.Valid src1838 dst1838 Finset.univ := by decide +kernel

def src1839 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,16,38,26,8,18,28,38]
def dst1839 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1839_0 : CycleData E W := ⟨3,![0,1,15,14,10],![2,6,4,28,14]⟩
def cycle1839_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1839_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1839_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1839_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle1839_5 : CycleData E W := ⟨2,![16,9,13,19],![6,16,14,26]⟩
def data1839 : PartitionData E W := ⟨6,![cycle1839_0,cycle1839_1,cycle1839_2,cycle1839_3,cycle1839_4,cycle1839_5]⟩
lemma valid_data1839 : data1839.Valid src1839 dst1839 Finset.univ := by decide +kernel

def src1840 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,16,38,26,8,18,38,28]
def dst1840 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1840_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1840_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1840_2 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle1840_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1840_4 : CycleData E W := ⟨2,![16,9,13,19],![6,16,14,26]⟩
def cycle1840_5 : CycleData E W := ⟨3,![11,12,18,22,15],![4,5,26,38,28]⟩
def data1840 : PartitionData E W := ⟨6,![cycle1840_0,cycle1840_1,cycle1840_2,cycle1840_3,cycle1840_4,cycle1840_5]⟩
lemma valid_data1840 : data1840.Valid src1840 dst1840 Finset.univ := by decide +kernel

def src1841 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,16,38,26,8,28,18,38]
def dst1841 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1841_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1841_1 : CycleData E W := ⟨3,![3,11,15,21,7],![3,5,4,28,18]⟩
def cycle1841_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1841_3 : CycleData E W := ⟨2,![5,20,14,10],![2,8,28,14]⟩
def cycle1841_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1841_5 : CycleData E W := ⟨2,![16,9,13,19],![6,16,14,26]⟩
def data1841 : PartitionData E W := ⟨6,![cycle1841_0,cycle1841_1,cycle1841_2,cycle1841_3,cycle1841_4,cycle1841_5]⟩
lemma valid_data1841 : data1841.Valid src1841 dst1841 Finset.univ := by decide +kernel

def src1842 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,26,16,38,8,18,28,38]
def dst1842 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1842_0 : CycleData E W := ⟨3,![0,1,15,14,10],![2,6,4,28,14]⟩
def cycle1842_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1842_2 : CycleData E W := ⟨3,![4,23,19,16,12],![5,8,38,6,26]⟩
def cycle1842_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1842_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle1842_5 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def data1842 : PartitionData E W := ⟨6,![cycle1842_0,cycle1842_1,cycle1842_2,cycle1842_3,cycle1842_4,cycle1842_5]⟩
lemma valid_data1842 : data1842.Valid src1842 dst1842 Finset.univ := by decide +kernel

def src1843 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,26,16,38,8,18,38,28]
def dst1843 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1843_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1843_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1843_2 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle1843_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1843_4 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def cycle1843_5 : CycleData E W := ⟨4,![11,12,16,19,22,15],![4,5,26,6,38,28]⟩
def data1843 : PartitionData E W := ⟨6,![cycle1843_0,cycle1843_1,cycle1843_2,cycle1843_3,cycle1843_4,cycle1843_5]⟩
lemma valid_data1843 : data1843.Valid src1843 dst1843 Finset.univ := by decide +kernel

def src1844 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,5,26,14,28,6,26,16,38,8,28,18,38]
def dst1844 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,5,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1844_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1844_1 : CycleData E W := ⟨3,![3,11,15,21,7],![3,5,4,28,18]⟩
def cycle1844_2 : CycleData E W := ⟨3,![4,23,19,16,12],![5,8,38,6,26]⟩
def cycle1844_3 : CycleData E W := ⟨2,![5,20,14,10],![2,8,28,14]⟩
def cycle1844_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1844_5 : CycleData E W := ⟨1,![9,17,13],![14,16,26]⟩
def data1844 : PartitionData E W := ⟨6,![cycle1844_0,cycle1844_1,cycle1844_2,cycle1844_3,cycle1844_4,cycle1844_5]⟩
lemma valid_data1844 : data1844.Valid src1844 dst1844 Finset.univ := by decide +kernel

def src1845 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,16,26,38,8,18,28,38]
def dst1845 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,16,26,38,6,18,28,38,8]
def cycle1845_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1845_1 : CycleData E W := ⟨2,![2,15,21,7],![3,4,28,18]⟩
def cycle1845_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,5,3]⟩
def cycle1845_3 : CycleData E W := ⟨3,![16,8,20,23,19],![6,16,18,8,38]⟩
def cycle1845_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle1845_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1845 : PartitionData E W := ⟨6,![cycle1845_0,cycle1845_1,cycle1845_2,cycle1845_3,cycle1845_4,cycle1845_5]⟩
lemma valid_data1845 : data1845.Valid src1845 dst1845 Finset.univ := by decide +kernel

def src1846 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,16,26,38,8,18,38,28]
def dst1846 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,16,26,38,6,18,38,28,8]
def cycle1846_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1846_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1846_2 : CycleData E W := ⟨3,![5,23,15,11,10],![2,8,28,4,14]⟩
def cycle1846_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1846_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle1846_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1846 : PartitionData E W := ⟨6,![cycle1846_0,cycle1846_1,cycle1846_2,cycle1846_3,cycle1846_4,cycle1846_5]⟩
lemma valid_data1846 : data1846.Valid src1846 dst1846 Finset.univ := by decide +kernel

def src1847 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,16,26,38,8,28,18,38]
def dst1847 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,16,26,38,6,28,18,38,8]
def cycle1847_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1847_1 : CycleData E W := ⟨2,![2,15,21,7],![3,4,28,18]⟩
def cycle1847_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,5,3]⟩
def cycle1847_3 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1847_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle1847_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1847 : PartitionData E W := ⟨6,![cycle1847_0,cycle1847_1,cycle1847_2,cycle1847_3,cycle1847_4,cycle1847_5]⟩
lemma valid_data1847 : data1847.Valid src1847 dst1847 Finset.univ := by decide +kernel

def src1848 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,16,38,26,8,18,28,38]
def dst1848 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,16,38,26,6,18,28,38,8]
def cycle1848_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1848_1 : CycleData E W := ⟨2,![2,15,21,7],![3,4,28,18]⟩
def cycle1848_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,5,3]⟩
def cycle1848_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle1848_4 : CycleData E W := ⟨3,![12,9,16,19,13],![5,14,16,6,26]⟩
def cycle1848_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1848 : PartitionData E W := ⟨6,![cycle1848_0,cycle1848_1,cycle1848_2,cycle1848_3,cycle1848_4,cycle1848_5]⟩
lemma valid_data1848 : data1848.Valid src1848 dst1848 Finset.univ := by decide +kernel

def src1849 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,16,38,26,8,18,38,28]
def dst1849 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,16,38,26,6,18,38,28,8]
def cycle1849_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1849_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1849_2 : CycleData E W := ⟨3,![5,23,15,11,10],![2,8,28,4,14]⟩
def cycle1849_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1849_4 : CycleData E W := ⟨3,![12,9,16,19,13],![5,14,16,6,26]⟩
def cycle1849_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1849 : PartitionData E W := ⟨6,![cycle1849_0,cycle1849_1,cycle1849_2,cycle1849_3,cycle1849_4,cycle1849_5]⟩
lemma valid_data1849 : data1849.Valid src1849 dst1849 Finset.univ := by decide +kernel

def src1850 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,16,38,26,8,28,18,38]
def dst1850 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,16,38,26,6,28,18,38,8]
def cycle1850_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1850_1 : CycleData E W := ⟨2,![2,15,21,7],![3,4,28,18]⟩
def cycle1850_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,5,3]⟩
def cycle1850_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1850_4 : CycleData E W := ⟨3,![12,9,16,19,13],![5,14,16,6,26]⟩
def cycle1850_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1850 : PartitionData E W := ⟨6,![cycle1850_0,cycle1850_1,cycle1850_2,cycle1850_3,cycle1850_4,cycle1850_5]⟩
lemma valid_data1850 : data1850.Valid src1850 dst1850 Finset.univ := by decide +kernel

def src1851 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,26,16,38,8,18,28,38]
def dst1851 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,26,16,38,6,18,28,38,8]
def cycle1851_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1851_1 : CycleData E W := ⟨2,![2,15,21,7],![3,4,28,18]⟩
def cycle1851_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,5,3]⟩
def cycle1851_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1851_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle1851_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1851 : PartitionData E W := ⟨6,![cycle1851_0,cycle1851_1,cycle1851_2,cycle1851_3,cycle1851_4,cycle1851_5]⟩
lemma valid_data1851 : data1851.Valid src1851 dst1851 Finset.univ := by decide +kernel

def src1852 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,26,16,38,8,18,38,28]
def dst1852 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,26,16,38,6,18,38,28,8]
def cycle1852_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1852_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1852_2 : CycleData E W := ⟨3,![5,23,15,11,10],![2,8,28,4,14]⟩
def cycle1852_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1852_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle1852_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1852 : PartitionData E W := ⟨6,![cycle1852_0,cycle1852_1,cycle1852_2,cycle1852_3,cycle1852_4,cycle1852_5]⟩
lemma valid_data1852 : data1852.Valid src1852 dst1852 Finset.univ := by decide +kernel

def src1853 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,5,26,28,6,26,16,38,8,28,18,38]
def dst1853 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,5,26,28,4,26,16,38,6,28,18,38,8]
def cycle1853_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1853_1 : CycleData E W := ⟨2,![2,15,21,7],![3,4,28,18]⟩
def cycle1853_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,5,3]⟩
def cycle1853_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1853_4 : CycleData E W := ⟨2,![12,9,17,13],![5,14,16,26]⟩
def cycle1853_5 : CycleData E W := ⟨3,![16,14,20,23,19],![6,26,28,8,38]⟩
def data1853 : PartitionData E W := ⟨6,![cycle1853_0,cycle1853_1,cycle1853_2,cycle1853_3,cycle1853_4,cycle1853_5]⟩
lemma valid_data1853 : data1853.Valid src1853 dst1853 Finset.univ := by decide +kernel

def src1854 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,16,26,38,8,18,28,38]
def dst1854 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,16,26,38,6,18,28,38,8]
def cycle1854_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1854_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle1854_2 : CycleData E W := ⟨2,![4,23,18,13],![5,8,38,26]⟩
def cycle1854_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1854_4 : CycleData E W := ⟨3,![16,8,21,22,19],![6,16,18,28,38]⟩
def cycle1854_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1854 : PartitionData E W := ⟨6,![cycle1854_0,cycle1854_1,cycle1854_2,cycle1854_3,cycle1854_4,cycle1854_5]⟩
lemma valid_data1854 : data1854.Valid src1854 dst1854 Finset.univ := by decide +kernel

def src1855 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,16,26,38,8,18,38,28]
def dst1855 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,16,26,38,6,18,38,28,8]
def cycle1855_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1855_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1855_2 : CycleData E W := ⟨3,![5,23,15,11,10],![2,8,28,4,14]⟩
def cycle1855_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1855_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle1855_5 : CycleData E W := ⟨2,![13,18,22,14],![5,26,38,28]⟩
def data1855 : PartitionData E W := ⟨6,![cycle1855_0,cycle1855_1,cycle1855_2,cycle1855_3,cycle1855_4,cycle1855_5]⟩
lemma valid_data1855 : data1855.Valid src1855 dst1855 Finset.univ := by decide +kernel

def src1856 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,16,26,38,8,28,18,38]
def dst1856 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,16,26,38,6,28,18,38,8]
def cycle1856_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1856_1 : CycleData E W := ⟨2,![3,14,21,7],![3,5,28,18]⟩
def cycle1856_2 : CycleData E W := ⟨2,![4,23,18,13],![5,8,38,26]⟩
def cycle1856_3 : CycleData E W := ⟨3,![5,20,15,11,10],![2,8,28,4,14]⟩
def cycle1856_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1856_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1856 : PartitionData E W := ⟨6,![cycle1856_0,cycle1856_1,cycle1856_2,cycle1856_3,cycle1856_4,cycle1856_5]⟩
lemma valid_data1856 : data1856.Valid src1856 dst1856 Finset.univ := by decide +kernel

def src1857 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,16,38,26,8,18,28,38]
def dst1857 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,16,38,26,6,18,28,38,8]
def cycle1857_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1857_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle1857_2 : CycleData E W := ⟨2,![4,23,18,13],![5,8,38,26]⟩
def cycle1857_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1857_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle1857_5 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def data1857 : PartitionData E W := ⟨6,![cycle1857_0,cycle1857_1,cycle1857_2,cycle1857_3,cycle1857_4,cycle1857_5]⟩
lemma valid_data1857 : data1857.Valid src1857 dst1857 Finset.univ := by decide +kernel

def src1858 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,16,38,26,8,18,38,28]
def dst1858 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,16,38,26,6,18,38,28,8]
def cycle1858_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1858_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1858_2 : CycleData E W := ⟨3,![5,23,15,11,10],![2,8,28,4,14]⟩
def cycle1858_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1858_4 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def cycle1858_5 : CycleData E W := ⟨2,![13,18,22,14],![5,26,38,28]⟩
def data1858 : PartitionData E W := ⟨6,![cycle1858_0,cycle1858_1,cycle1858_2,cycle1858_3,cycle1858_4,cycle1858_5]⟩
lemma valid_data1858 : data1858.Valid src1858 dst1858 Finset.univ := by decide +kernel

def src1859 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,16,38,26,8,28,18,38]
def dst1859 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,16,38,26,6,28,18,38,8]
def cycle1859_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1859_1 : CycleData E W := ⟨2,![3,14,21,7],![3,5,28,18]⟩
def cycle1859_2 : CycleData E W := ⟨2,![4,23,18,13],![5,8,38,26]⟩
def cycle1859_3 : CycleData E W := ⟨3,![5,20,15,11,10],![2,8,28,4,14]⟩
def cycle1859_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1859_5 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def data1859 : PartitionData E W := ⟨6,![cycle1859_0,cycle1859_1,cycle1859_2,cycle1859_3,cycle1859_4,cycle1859_5]⟩
lemma valid_data1859 : data1859.Valid src1859 dst1859 Finset.univ := by decide +kernel

def src1860 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,26,16,38,8,18,28,38]
def dst1860 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,26,16,38,6,18,28,38,8]
def cycle1860_0 : CycleData E W := ⟨2,![0,1,11,10],![2,6,4,14]⟩
def cycle1860_1 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle1860_2 : CycleData E W := ⟨3,![4,23,19,16,13],![5,8,38,6,26]⟩
def cycle1860_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1860_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle1860_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1860 : PartitionData E W := ⟨6,![cycle1860_0,cycle1860_1,cycle1860_2,cycle1860_3,cycle1860_4,cycle1860_5]⟩
lemma valid_data1860 : data1860.Valid src1860 dst1860 Finset.univ := by decide +kernel

def src1861 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,26,16,38,8,18,38,28]
def dst1861 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,26,16,38,6,18,38,28,8]
def cycle1861_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1861_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1861_2 : CycleData E W := ⟨3,![5,23,15,11,10],![2,8,28,4,14]⟩
def cycle1861_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1861_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle1861_5 : CycleData E W := ⟨3,![13,16,19,22,14],![5,26,6,38,28]⟩
def data1861 : PartitionData E W := ⟨6,![cycle1861_0,cycle1861_1,cycle1861_2,cycle1861_3,cycle1861_4,cycle1861_5]⟩
lemma valid_data1861 : data1861.Valid src1861 dst1861 Finset.univ := by decide +kernel

def src1862 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,14,26,5,28,6,26,16,38,8,28,18,38]
def dst1862 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,14,26,5,28,4,26,16,38,6,28,18,38,8]
def cycle1862_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1862_1 : CycleData E W := ⟨2,![3,14,21,7],![3,5,28,18]⟩
def cycle1862_2 : CycleData E W := ⟨3,![4,23,19,16,13],![5,8,38,6,26]⟩
def cycle1862_3 : CycleData E W := ⟨3,![5,20,15,11,10],![2,8,28,4,14]⟩
def cycle1862_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1862_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1862 : PartitionData E W := ⟨6,![cycle1862_0,cycle1862_1,cycle1862_2,cycle1862_3,cycle1862_4,cycle1862_5]⟩
lemma valid_data1862 : data1862.Valid src1862 dst1862 Finset.univ := by decide +kernel

def src1863 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst1863 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle1863_0 : CycleData E W := ⟨10,![0,19,18,11,15,14,9,8,20,4,3,6],![2,6,38,26,4,28,14,16,18,8,5,3]⟩
def cycle1863_1 : CycleData E W := ⟨10,![5,23,22,21,7,2,1,16,17,12,13,10],![2,8,38,28,18,3,4,6,16,26,5,14]⟩
def data1863 : PartitionData E W := ⟨2,![cycle1863_0,cycle1863_1]⟩
lemma valid_data1863 : data1863.Valid src1863 dst1863 Finset.univ := by decide +kernel

def src1864 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst1864 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle1864_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1864_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1864_2 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle1864_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1864_4 : CycleData E W := ⟨2,![12,17,9,13],![5,26,16,14]⟩
def cycle1864_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1864 : PartitionData E W := ⟨6,![cycle1864_0,cycle1864_1,cycle1864_2,cycle1864_3,cycle1864_4,cycle1864_5]⟩
lemma valid_data1864 : data1864.Valid src1864 dst1864 Finset.univ := by decide +kernel

def src1865 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,16,26,38,8,28,18,38]
def dst1865 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,16,26,38,6,28,18,38,8]
def cycle1865_0 : CycleData E W := ⟨10,![0,19,18,11,15,20,4,3,7,8,9,10],![2,6,38,26,4,28,8,5,3,18,16,14]⟩
def cycle1865_1 : CycleData E W := ⟨10,![5,23,22,21,14,13,12,17,16,1,2,6],![2,8,38,18,28,14,5,26,16,6,4,3]⟩
def data1865 : PartitionData E W := ⟨2,![cycle1865_0,cycle1865_1]⟩
lemma valid_data1865 : data1865.Valid src1865 dst1865 Finset.univ := by decide +kernel

def src1866 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,16,38,26,8,18,28,38]
def dst1866 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,16,38,26,6,18,28,38,8]
def cycle1866_0 : CycleData E W := ⟨2,![0,16,9,10],![2,6,16,14]⟩
def cycle1866_1 : CycleData E W := ⟨1,![1,19,11],![4,6,26]⟩
def cycle1866_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle1866_3 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1866_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1866_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data1866 : PartitionData E W := ⟨6,![cycle1866_0,cycle1866_1,cycle1866_2,cycle1866_3,cycle1866_4,cycle1866_5]⟩
lemma valid_data1866 : data1866.Valid src1866 dst1866 Finset.univ := by decide +kernel

def src1867 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,16,38,26,8,18,38,28]
def dst1867 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,16,38,26,6,18,38,28,8]
def cycle1867_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1867_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1867_2 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle1867_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1867_4 : CycleData E W := ⟨3,![12,19,16,9,13],![5,26,6,16,14]⟩
def cycle1867_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1867 : PartitionData E W := ⟨6,![cycle1867_0,cycle1867_1,cycle1867_2,cycle1867_3,cycle1867_4,cycle1867_5]⟩
lemma valid_data1867 : data1867.Valid src1867 dst1867 Finset.univ := by decide +kernel

def src1868 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,16,38,26,8,28,18,38]
def dst1868 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,16,38,26,6,28,18,38,8]
def cycle1868_0 : CycleData E W := ⟨2,![0,16,9,10],![2,6,16,14]⟩
def cycle1868_1 : CycleData E W := ⟨1,![1,19,11],![4,6,26]⟩
def cycle1868_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle1868_3 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1868_4 : CycleData E W := ⟨3,![5,20,21,7,6],![2,8,28,18,3]⟩
def cycle1868_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1868 : PartitionData E W := ⟨6,![cycle1868_0,cycle1868_1,cycle1868_2,cycle1868_3,cycle1868_4,cycle1868_5]⟩
lemma valid_data1868 : data1868.Valid src1868 dst1868 Finset.univ := by decide +kernel

def src1869 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,26,16,38,8,18,28,38]
def dst1869 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,26,16,38,6,18,28,38,8]
def cycle1869_0 : CycleData E W := ⟨3,![0,19,22,14,10],![2,6,38,28,14]⟩
def cycle1869_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle1869_2 : CycleData E W := ⟨2,![2,15,21,7],![3,4,28,18]⟩
def cycle1869_3 : CycleData E W := ⟨2,![5,4,3,6],![2,8,5,3]⟩
def cycle1869_4 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1869_5 : CycleData E W := ⟨2,![12,17,9,13],![5,26,16,14]⟩
def data1869 : PartitionData E W := ⟨6,![cycle1869_0,cycle1869_1,cycle1869_2,cycle1869_3,cycle1869_4,cycle1869_5]⟩
lemma valid_data1869 : data1869.Valid src1869 dst1869 Finset.univ := by decide +kernel

def src1870 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,26,16,38,8,18,38,28]
def dst1870 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,26,16,38,6,18,38,28,8]
def cycle1870_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,4,3]⟩
def cycle1870_1 : CycleData E W := ⟨2,![3,4,20,7],![3,5,8,18]⟩
def cycle1870_2 : CycleData E W := ⟨2,![5,23,14,10],![2,8,28,14]⟩
def cycle1870_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1870_4 : CycleData E W := ⟨2,![12,17,9,13],![5,26,16,14]⟩
def cycle1870_5 : CycleData E W := ⟨3,![11,16,19,22,15],![4,26,6,38,28]⟩
def data1870 : PartitionData E W := ⟨6,![cycle1870_0,cycle1870_1,cycle1870_2,cycle1870_3,cycle1870_4,cycle1870_5]⟩
lemma valid_data1870 : data1870.Valid src1870 dst1870 Finset.univ := by decide +kernel

def src1871 : E → W := ![2,6,4,3,5,8,2,3,18,16,14,4,26,5,14,28,6,26,16,38,8,28,18,38]
def dst1871 : E → W := ![6,4,3,5,8,2,3,18,16,14,2,26,5,14,28,4,26,16,38,6,28,18,38,8]
def cycle1871_0 : CycleData E W := ⟨2,![0,19,23,5],![2,6,38,8]⟩
def cycle1871_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle1871_2 : CycleData E W := ⟨3,![6,2,15,14,10],![2,3,4,28,14]⟩
def cycle1871_3 : CycleData E W := ⟨3,![3,4,20,21,7],![3,5,8,28,18]⟩
def cycle1871_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1871_5 : CycleData E W := ⟨2,![12,17,9,13],![5,26,16,14]⟩
def data1871 : PartitionData E W := ⟨6,![cycle1871_0,cycle1871_1,cycle1871_2,cycle1871_3,cycle1871_4,cycle1871_5]⟩
lemma valid_data1871 : data1871.Valid src1871 dst1871 Finset.univ := by decide +kernel

def src1872 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,16,26,38,8,18,28,38]
def dst1872 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1872_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1872_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1872_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1872_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1872_4 : CycleData E W := ⟨2,![7,13,17,8],![3,14,26,16]⟩
def cycle1872_5 : CycleData E W := ⟨3,![16,9,21,22,19],![6,16,18,28,38]⟩
def data1872 : PartitionData E W := ⟨6,![cycle1872_0,cycle1872_1,cycle1872_2,cycle1872_3,cycle1872_4,cycle1872_5]⟩
lemma valid_data1872 : data1872.Valid src1872 dst1872 Finset.univ := by decide +kernel

def src1873 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,16,26,38,8,18,38,28]
def dst1873 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1873_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,6,4,3,14]⟩
def cycle1873_1 : CycleData E W := ⟨2,![3,12,17,8],![3,5,26,16]⟩
def cycle1873_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1873_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1873_4 : CycleData E W := ⟨2,![16,9,21,19],![6,16,18,38]⟩
def cycle1873_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1873 : PartitionData E W := ⟨6,![cycle1873_0,cycle1873_1,cycle1873_2,cycle1873_3,cycle1873_4,cycle1873_5]⟩
lemma valid_data1873 : data1873.Valid src1873 dst1873 Finset.univ := by decide +kernel

def src1874 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,16,26,38,8,28,18,38]
def dst1874 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1874_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1874_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1874_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1874_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle1874_4 : CycleData E W := ⟨2,![7,13,17,8],![3,14,26,16]⟩
def cycle1874_5 : CycleData E W := ⟨2,![16,9,22,19],![6,16,18,38]⟩
def data1874 : PartitionData E W := ⟨6,![cycle1874_0,cycle1874_1,cycle1874_2,cycle1874_3,cycle1874_4,cycle1874_5]⟩
lemma valid_data1874 : data1874.Valid src1874 dst1874 Finset.univ := by decide +kernel

def src1875 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,16,38,26,8,18,28,38]
def dst1875 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1875_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1875_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1875_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1875_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1875_4 : CycleData E W := ⟨3,![7,13,19,16,8],![3,14,26,6,16]⟩
def cycle1875_5 : CycleData E W := ⟨2,![9,21,22,17],![16,18,28,38]⟩
def data1875 : PartitionData E W := ⟨6,![cycle1875_0,cycle1875_1,cycle1875_2,cycle1875_3,cycle1875_4,cycle1875_5]⟩
lemma valid_data1875 : data1875.Valid src1875 dst1875 Finset.univ := by decide +kernel

def src1876 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,16,38,26,8,18,38,28]
def dst1876 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1876_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,6,4,3,14]⟩
def cycle1876_1 : CycleData E W := ⟨3,![3,12,19,16,8],![3,5,26,6,16]⟩
def cycle1876_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1876_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1876_4 : CycleData E W := ⟨1,![9,21,17],![16,18,38]⟩
def cycle1876_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1876 : PartitionData E W := ⟨6,![cycle1876_0,cycle1876_1,cycle1876_2,cycle1876_3,cycle1876_4,cycle1876_5]⟩
lemma valid_data1876 : data1876.Valid src1876 dst1876 Finset.univ := by decide +kernel

def src1877 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,16,38,26,8,28,18,38]
def dst1877 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1877_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1877_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1877_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1877_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle1877_4 : CycleData E W := ⟨3,![7,13,19,16,8],![3,14,26,6,16]⟩
def cycle1877_5 : CycleData E W := ⟨1,![9,22,17],![16,18,38]⟩
def data1877 : PartitionData E W := ⟨6,![cycle1877_0,cycle1877_1,cycle1877_2,cycle1877_3,cycle1877_4,cycle1877_5]⟩
lemma valid_data1877 : data1877.Valid src1877 dst1877 Finset.univ := by decide +kernel

def src1878 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,26,16,38,8,18,28,38]
def dst1878 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1878_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1878_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1878_2 : CycleData E W := ⟨3,![4,23,19,16,12],![5,8,38,6,26]⟩
def cycle1878_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1878_4 : CycleData E W := ⟨2,![7,13,17,8],![3,14,26,16]⟩
def cycle1878_5 : CycleData E W := ⟨2,![9,21,22,18],![16,18,28,38]⟩
def data1878 : PartitionData E W := ⟨6,![cycle1878_0,cycle1878_1,cycle1878_2,cycle1878_3,cycle1878_4,cycle1878_5]⟩
lemma valid_data1878 : data1878.Valid src1878 dst1878 Finset.univ := by decide +kernel

def src1879 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,26,16,38,8,18,38,28]
def dst1879 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1879_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,6,4,3,14]⟩
def cycle1879_1 : CycleData E W := ⟨2,![3,12,17,8],![3,5,26,16]⟩
def cycle1879_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1879_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1879_4 : CycleData E W := ⟨1,![9,21,18],![16,18,38]⟩
def cycle1879_5 : CycleData E W := ⟨3,![16,13,14,22,19],![6,26,14,28,38]⟩
def data1879 : PartitionData E W := ⟨6,![cycle1879_0,cycle1879_1,cycle1879_2,cycle1879_3,cycle1879_4,cycle1879_5]⟩
lemma valid_data1879 : data1879.Valid src1879 dst1879 Finset.univ := by decide +kernel

def src1880 : E → W := ![2,6,4,3,5,8,2,14,3,16,18,4,5,26,14,28,6,26,16,38,8,28,18,38]
def dst1880 : E → W := ![6,4,3,5,8,2,14,3,16,18,2,5,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1880_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1880_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1880_2 : CycleData E W := ⟨3,![4,23,19,16,12],![5,8,38,6,26]⟩
def cycle1880_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle1880_4 : CycleData E W := ⟨2,![7,13,17,8],![3,14,26,16]⟩
def cycle1880_5 : CycleData E W := ⟨1,![9,22,18],![16,18,38]⟩
def data1880 : PartitionData E W := ⟨6,![cycle1880_0,cycle1880_1,cycle1880_2,cycle1880_3,cycle1880_4,cycle1880_5]⟩
lemma valid_data1880 : data1880.Valid src1880 dst1880 Finset.univ := by decide +kernel

def src1881 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,16,26,38,8,18,28,38]
def dst1881 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1881_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1881_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1881_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1881_3 : CycleData E W := ⟨3,![5,4,12,13,6],![2,8,5,26,14]⟩
def cycle1881_4 : CycleData E W := ⟨2,![7,14,21,8],![3,14,28,18]⟩
def cycle1881_5 : CycleData E W := ⟨3,![20,9,17,18,23],![8,18,16,26,38]⟩
def data1881 : PartitionData E W := ⟨6,![cycle1881_0,cycle1881_1,cycle1881_2,cycle1881_3,cycle1881_4,cycle1881_5]⟩
lemma valid_data1881 : data1881.Valid src1881 dst1881 Finset.univ := by decide +kernel

def src1882 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,16,26,38,8,18,38,28]
def dst1882 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1882_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1882_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1882_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1882_3 : CycleData E W := ⟨3,![5,4,12,13,6],![2,8,5,26,14]⟩
def cycle1882_4 : CycleData E W := ⟨3,![7,14,23,20,8],![3,14,28,8,18]⟩
def cycle1882_5 : CycleData E W := ⟨2,![9,21,18,17],![16,18,38,26]⟩
def data1882 : PartitionData E W := ⟨6,![cycle1882_0,cycle1882_1,cycle1882_2,cycle1882_3,cycle1882_4,cycle1882_5]⟩
lemma valid_data1882 : data1882.Valid src1882 dst1882 Finset.univ := by decide +kernel

def src1883 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,16,26,38,8,28,18,38]
def dst1883 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1883_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1883_1 : CycleData E W := ⟨3,![1,19,22,21,15],![4,6,38,18,28]⟩
def cycle1883_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1883_3 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1883_4 : CycleData E W := ⟨2,![5,20,14,6],![2,8,28,14]⟩
def cycle1883_5 : CycleData E W := ⟨3,![7,13,17,9,8],![3,14,26,16,18]⟩
def data1883 : PartitionData E W := ⟨6,![cycle1883_0,cycle1883_1,cycle1883_2,cycle1883_3,cycle1883_4,cycle1883_5]⟩
lemma valid_data1883 : data1883.Valid src1883 dst1883 Finset.univ := by decide +kernel

def src1884 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,16,38,26,8,18,28,38]
def dst1884 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1884_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1884_1 : CycleData E W := ⟨2,![1,19,12,11],![4,6,26,5]⟩
def cycle1884_2 : CycleData E W := ⟨2,![2,15,14,7],![3,4,28,14]⟩
def cycle1884_3 : CycleData E W := ⟨2,![3,4,20,8],![3,5,8,18]⟩
def cycle1884_4 : CycleData E W := ⟨3,![5,23,18,13,6],![2,8,38,26,14]⟩
def cycle1884_5 : CycleData E W := ⟨2,![9,21,22,17],![16,18,28,38]⟩
def data1884 : PartitionData E W := ⟨6,![cycle1884_0,cycle1884_1,cycle1884_2,cycle1884_3,cycle1884_4,cycle1884_5]⟩
lemma valid_data1884 : data1884.Valid src1884 dst1884 Finset.univ := by decide +kernel

def src1885 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,16,38,26,8,18,38,28]
def dst1885 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1885_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1885_1 : CycleData E W := ⟨3,![2,1,19,12,3],![3,4,6,26,5]⟩
def cycle1885_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1885_3 : CycleData E W := ⟨3,![5,20,8,7,6],![2,8,18,3,14]⟩
def cycle1885_4 : CycleData E W := ⟨1,![9,21,17],![16,18,38]⟩
def cycle1885_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1885 : PartitionData E W := ⟨6,![cycle1885_0,cycle1885_1,cycle1885_2,cycle1885_3,cycle1885_4,cycle1885_5]⟩
lemma valid_data1885 : data1885.Valid src1885 dst1885 Finset.univ := by decide +kernel

def src1886 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,16,38,26,8,28,18,38]
def dst1886 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1886_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1886_1 : CycleData E W := ⟨3,![2,1,19,12,3],![3,4,6,26,5]⟩
def cycle1886_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle1886_3 : CycleData E W := ⟨3,![5,23,18,13,6],![2,8,38,26,14]⟩
def cycle1886_4 : CycleData E W := ⟨2,![7,14,21,8],![3,14,28,18]⟩
def cycle1886_5 : CycleData E W := ⟨1,![9,22,17],![16,18,38]⟩
def data1886 : PartitionData E W := ⟨6,![cycle1886_0,cycle1886_1,cycle1886_2,cycle1886_3,cycle1886_4,cycle1886_5]⟩
lemma valid_data1886 : data1886.Valid src1886 dst1886 Finset.univ := by decide +kernel

def src1887 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,26,16,38,8,18,28,38]
def dst1887 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1887_0 : CycleData E W := ⟨3,![0,16,12,4,5],![2,6,26,5,8]⟩
def cycle1887_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1887_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1887_3 : CycleData E W := ⟨2,![6,13,17,10],![2,14,26,16]⟩
def cycle1887_4 : CycleData E W := ⟨2,![7,14,21,8],![3,14,28,18]⟩
def cycle1887_5 : CycleData E W := ⟨2,![20,9,18,23],![8,18,16,38]⟩
def data1887 : PartitionData E W := ⟨6,![cycle1887_0,cycle1887_1,cycle1887_2,cycle1887_3,cycle1887_4,cycle1887_5]⟩
lemma valid_data1887 : data1887.Valid src1887 dst1887 Finset.univ := by decide +kernel

def src1888 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,26,16,38,8,18,38,28]
def dst1888 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1888_0 : CycleData E W := ⟨3,![0,16,12,4,5],![2,6,26,5,8]⟩
def cycle1888_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1888_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1888_3 : CycleData E W := ⟨2,![6,13,17,10],![2,14,26,16]⟩
def cycle1888_4 : CycleData E W := ⟨3,![7,14,23,20,8],![3,14,28,8,18]⟩
def cycle1888_5 : CycleData E W := ⟨1,![9,21,18],![16,18,38]⟩
def data1888 : PartitionData E W := ⟨6,![cycle1888_0,cycle1888_1,cycle1888_2,cycle1888_3,cycle1888_4,cycle1888_5]⟩
lemma valid_data1888 : data1888.Valid src1888 dst1888 Finset.univ := by decide +kernel

def src1889 : E → W := ![2,6,4,3,5,8,2,14,3,18,16,4,5,26,14,28,6,26,16,38,8,28,18,38]
def dst1889 : E → W := ![6,4,3,5,8,2,14,3,18,16,2,5,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1889_0 : CycleData E W := ⟨3,![0,16,12,4,5],![2,6,26,5,8]⟩
def cycle1889_1 : CycleData E W := ⟨3,![1,19,23,20,15],![4,6,38,8,28]⟩
def cycle1889_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1889_3 : CycleData E W := ⟨2,![6,13,17,10],![2,14,26,16]⟩
def cycle1889_4 : CycleData E W := ⟨2,![7,14,21,8],![3,14,28,18]⟩
def cycle1889_5 : CycleData E W := ⟨1,![9,22,18],![16,18,38]⟩
def data1889 : PartitionData E W := ⟨6,![cycle1889_0,cycle1889_1,cycle1889_2,cycle1889_3,cycle1889_4,cycle1889_5]⟩
lemma valid_data1889 : data1889.Valid src1889 dst1889 Finset.univ := by decide +kernel

def src1890 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,16,26,38,8,18,28,38]
def dst1890 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1890_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1890_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1890_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1890_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1890_4 : CycleData E W := ⟨1,![7,17,13],![14,16,26]⟩
def cycle1890_5 : CycleData E W := ⟨4,![8,16,19,22,21,9],![3,16,6,38,28,18]⟩
def data1890 : PartitionData E W := ⟨6,![cycle1890_0,cycle1890_1,cycle1890_2,cycle1890_3,cycle1890_4,cycle1890_5]⟩
lemma valid_data1890 : data1890.Valid src1890 dst1890 Finset.univ := by decide +kernel

def src1891 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,16,26,38,8,18,38,28]
def dst1891 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1891_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1891_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1891_2 : CycleData E W := ⟨3,![4,23,22,18,12],![5,8,28,38,26]⟩
def cycle1891_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1891_4 : CycleData E W := ⟨1,![7,17,13],![14,16,26]⟩
def cycle1891_5 : CycleData E W := ⟨3,![8,16,19,21,9],![3,16,6,38,18]⟩
def data1891 : PartitionData E W := ⟨6,![cycle1891_0,cycle1891_1,cycle1891_2,cycle1891_3,cycle1891_4,cycle1891_5]⟩
lemma valid_data1891 : data1891.Valid src1891 dst1891 Finset.univ := by decide +kernel

def src1892 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,16,26,38,8,28,18,38]
def dst1892 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1892_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1892_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1892_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1892_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle1892_4 : CycleData E W := ⟨1,![7,17,13],![14,16,26]⟩
def cycle1892_5 : CycleData E W := ⟨3,![8,16,19,22,9],![3,16,6,38,18]⟩
def data1892 : PartitionData E W := ⟨6,![cycle1892_0,cycle1892_1,cycle1892_2,cycle1892_3,cycle1892_4,cycle1892_5]⟩
lemma valid_data1892 : data1892.Valid src1892 dst1892 Finset.univ := by decide +kernel

def src1893 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,16,38,26,8,18,28,38]
def dst1893 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1893_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1893_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1893_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1893_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1893_4 : CycleData E W := ⟨2,![16,7,13,19],![6,16,14,26]⟩
def cycle1893_5 : CycleData E W := ⟨3,![8,17,22,21,9],![3,16,38,28,18]⟩
def data1893 : PartitionData E W := ⟨6,![cycle1893_0,cycle1893_1,cycle1893_2,cycle1893_3,cycle1893_4,cycle1893_5]⟩
lemma valid_data1893 : data1893.Valid src1893 dst1893 Finset.univ := by decide +kernel

def src1894 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,16,38,26,8,18,38,28]
def dst1894 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1894_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1894_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1894_2 : CycleData E W := ⟨3,![4,23,22,18,12],![5,8,28,38,26]⟩
def cycle1894_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1894_4 : CycleData E W := ⟨2,![16,7,13,19],![6,16,14,26]⟩
def cycle1894_5 : CycleData E W := ⟨2,![8,17,21,9],![3,16,38,18]⟩
def data1894 : PartitionData E W := ⟨6,![cycle1894_0,cycle1894_1,cycle1894_2,cycle1894_3,cycle1894_4,cycle1894_5]⟩
lemma valid_data1894 : data1894.Valid src1894 dst1894 Finset.univ := by decide +kernel

def src1895 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,16,38,26,8,28,18,38]
def dst1895 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1895_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1895_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1895_2 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1895_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle1895_4 : CycleData E W := ⟨2,![16,7,13,19],![6,16,14,26]⟩
def cycle1895_5 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def data1895 : PartitionData E W := ⟨6,![cycle1895_0,cycle1895_1,cycle1895_2,cycle1895_3,cycle1895_4,cycle1895_5]⟩
lemma valid_data1895 : data1895.Valid src1895 dst1895 Finset.univ := by decide +kernel

def src1896 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,26,16,38,8,18,28,38]
def dst1896 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1896_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1896_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1896_2 : CycleData E W := ⟨3,![4,23,19,16,12],![5,8,38,6,26]⟩
def cycle1896_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1896_4 : CycleData E W := ⟨1,![7,17,13],![14,16,26]⟩
def cycle1896_5 : CycleData E W := ⟨3,![8,18,22,21,9],![3,16,38,28,18]⟩
def data1896 : PartitionData E W := ⟨6,![cycle1896_0,cycle1896_1,cycle1896_2,cycle1896_3,cycle1896_4,cycle1896_5]⟩
lemma valid_data1896 : data1896.Valid src1896 dst1896 Finset.univ := by decide +kernel

def src1897 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,26,16,38,8,18,38,28]
def dst1897 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1897_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1897_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1897_2 : CycleData E W := ⟨4,![4,23,22,19,16,12],![5,8,28,38,6,26]⟩
def cycle1897_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1897_4 : CycleData E W := ⟨1,![7,17,13],![14,16,26]⟩
def cycle1897_5 : CycleData E W := ⟨2,![8,18,21,9],![3,16,38,18]⟩
def data1897 : PartitionData E W := ⟨6,![cycle1897_0,cycle1897_1,cycle1897_2,cycle1897_3,cycle1897_4,cycle1897_5]⟩
lemma valid_data1897 : data1897.Valid src1897 dst1897 Finset.univ := by decide +kernel

def src1898 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,5,26,14,28,6,26,16,38,8,28,18,38]
def dst1898 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,5,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1898_0 : CycleData E W := ⟨3,![0,1,15,14,6],![2,6,4,28,14]⟩
def cycle1898_1 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1898_2 : CycleData E W := ⟨3,![4,23,19,16,12],![5,8,38,6,26]⟩
def cycle1898_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle1898_4 : CycleData E W := ⟨1,![7,17,13],![14,16,26]⟩
def cycle1898_5 : CycleData E W := ⟨2,![8,18,22,9],![3,16,38,18]⟩
def data1898 : PartitionData E W := ⟨6,![cycle1898_0,cycle1898_1,cycle1898_2,cycle1898_3,cycle1898_4,cycle1898_5]⟩
lemma valid_data1898 : data1898.Valid src1898 dst1898 Finset.univ := by decide +kernel

def src1899 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,18,28,38]
def dst1899 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,18,28,38,8]
def cycle1899_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle1899_1 : CycleData E W := ⟨2,![1,19,18,11],![4,6,38,26]⟩
def cycle1899_2 : CycleData E W := ⟨2,![2,15,21,9],![3,4,28,18]⟩
def cycle1899_3 : CycleData E W := ⟨2,![3,12,17,8],![3,5,26,16]⟩
def cycle1899_4 : CycleData E W := ⟨3,![4,23,22,14,13],![5,8,38,28,14]⟩
def cycle1899_5 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def data1899 : PartitionData E W := ⟨6,![cycle1899_0,cycle1899_1,cycle1899_2,cycle1899_3,cycle1899_4,cycle1899_5]⟩
lemma valid_data1899 : data1899.Valid src1899 dst1899 Finset.univ := by decide +kernel

def src1900 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,18,38,28]
def dst1900 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,18,38,28,8]
def cycle1900_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle1900_1 : CycleData E W := ⟨2,![1,19,18,11],![4,6,38,26]⟩
def cycle1900_2 : CycleData E W := ⟨3,![2,15,22,21,9],![3,4,28,38,18]⟩
def cycle1900_3 : CycleData E W := ⟨2,![3,12,17,8],![3,5,26,16]⟩
def cycle1900_4 : CycleData E W := ⟨2,![4,23,14,13],![5,8,28,14]⟩
def cycle1900_5 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def data1900 : PartitionData E W := ⟨6,![cycle1900_0,cycle1900_1,cycle1900_2,cycle1900_3,cycle1900_4,cycle1900_5]⟩
lemma valid_data1900 : data1900.Valid src1900 dst1900 Finset.univ := by decide +kernel

def src1901 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,26,38,8,28,18,38]
def dst1901 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,26,38,6,28,18,38,8]
def cycle1901_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle1901_1 : CycleData E W := ⟨2,![1,19,18,11],![4,6,38,26]⟩
def cycle1901_2 : CycleData E W := ⟨2,![2,15,21,9],![3,4,28,18]⟩
def cycle1901_3 : CycleData E W := ⟨2,![3,12,17,8],![3,5,26,16]⟩
def cycle1901_4 : CycleData E W := ⟨2,![4,20,14,13],![5,8,28,14]⟩
def cycle1901_5 : CycleData E W := ⟨2,![5,23,22,10],![2,8,38,18]⟩
def data1901 : PartitionData E W := ⟨6,![cycle1901_0,cycle1901_1,cycle1901_2,cycle1901_3,cycle1901_4,cycle1901_5]⟩
lemma valid_data1901 : data1901.Valid src1901 dst1901 Finset.univ := by decide +kernel

def src1902 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,18,28,38]
def dst1902 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,18,28,38,8]
def cycle1902_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle1902_1 : CycleData E W := ⟨1,![1,19,11],![4,6,26]⟩
def cycle1902_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle1902_3 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1902_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1902_5 : CycleData E W := ⟨3,![8,17,22,21,9],![3,16,38,28,18]⟩
def data1902 : PartitionData E W := ⟨6,![cycle1902_0,cycle1902_1,cycle1902_2,cycle1902_3,cycle1902_4,cycle1902_5]⟩
lemma valid_data1902 : data1902.Valid src1902 dst1902 Finset.univ := by decide +kernel

def src1903 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,18,38,28]
def dst1903 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,18,38,28,8]
def cycle1903_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle1903_1 : CycleData E W := ⟨1,![1,19,11],![4,6,26]⟩
def cycle1903_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle1903_3 : CycleData E W := ⟨3,![4,23,22,18,12],![5,8,28,38,26]⟩
def cycle1903_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1903_5 : CycleData E W := ⟨2,![8,17,21,9],![3,16,38,18]⟩
def data1903 : PartitionData E W := ⟨6,![cycle1903_0,cycle1903_1,cycle1903_2,cycle1903_3,cycle1903_4,cycle1903_5]⟩
lemma valid_data1903 : data1903.Valid src1903 dst1903 Finset.univ := by decide +kernel

def src1904 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,16,38,26,8,28,18,38]
def dst1904 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,16,38,26,6,28,18,38,8]
def cycle1904_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle1904_1 : CycleData E W := ⟨1,![1,19,11],![4,6,26]⟩
def cycle1904_2 : CycleData E W := ⟨3,![2,15,14,13,3],![3,4,28,14,5]⟩
def cycle1904_3 : CycleData E W := ⟨2,![4,23,18,12],![5,8,38,26]⟩
def cycle1904_4 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle1904_5 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def data1904 : PartitionData E W := ⟨6,![cycle1904_0,cycle1904_1,cycle1904_2,cycle1904_3,cycle1904_4,cycle1904_5]⟩
lemma valid_data1904 : data1904.Valid src1904 dst1904 Finset.univ := by decide +kernel

def src1905 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,18,28,38]
def dst1905 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,18,28,38,8]
def cycle1905_0 : CycleData E W := ⟨3,![0,19,18,7,6],![2,6,38,16,14]⟩
def cycle1905_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle1905_2 : CycleData E W := ⟨2,![2,15,21,9],![3,4,28,18]⟩
def cycle1905_3 : CycleData E W := ⟨2,![3,12,17,8],![3,5,26,16]⟩
def cycle1905_4 : CycleData E W := ⟨3,![4,23,22,14,13],![5,8,38,28,14]⟩
def cycle1905_5 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def data1905 : PartitionData E W := ⟨6,![cycle1905_0,cycle1905_1,cycle1905_2,cycle1905_3,cycle1905_4,cycle1905_5]⟩
lemma valid_data1905 : data1905.Valid src1905 dst1905 Finset.univ := by decide +kernel

def src1906 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,18,38,28]
def dst1906 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,18,38,28,8]
def cycle1906_0 : CycleData E W := ⟨3,![0,16,17,7,6],![2,6,26,16,14]⟩
def cycle1906_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1906_2 : CycleData E W := ⟨2,![2,11,12,3],![3,4,26,5]⟩
def cycle1906_3 : CycleData E W := ⟨2,![4,23,14,13],![5,8,28,14]⟩
def cycle1906_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1906_5 : CycleData E W := ⟨2,![8,18,21,9],![3,16,38,18]⟩
def data1906 : PartitionData E W := ⟨6,![cycle1906_0,cycle1906_1,cycle1906_2,cycle1906_3,cycle1906_4,cycle1906_5]⟩
lemma valid_data1906 : data1906.Valid src1906 dst1906 Finset.univ := by decide +kernel

def src1907 : E → W := ![2,6,4,3,5,8,2,14,16,3,18,4,26,5,14,28,6,26,16,38,8,28,18,38]
def dst1907 : E → W := ![6,4,3,5,8,2,14,16,3,18,2,26,5,14,28,4,26,16,38,6,28,18,38,8]
def cycle1907_0 : CycleData E W := ⟨3,![0,19,18,7,6],![2,6,38,16,14]⟩
def cycle1907_1 : CycleData E W := ⟨1,![1,16,11],![4,6,26]⟩
def cycle1907_2 : CycleData E W := ⟨2,![2,15,21,9],![3,4,28,18]⟩
def cycle1907_3 : CycleData E W := ⟨2,![3,12,17,8],![3,5,26,16]⟩
def cycle1907_4 : CycleData E W := ⟨2,![4,20,14,13],![5,8,28,14]⟩
def cycle1907_5 : CycleData E W := ⟨2,![5,23,22,10],![2,8,38,18]⟩
def data1907 : PartitionData E W := ⟨6,![cycle1907_0,cycle1907_1,cycle1907_2,cycle1907_3,cycle1907_4,cycle1907_5]⟩
lemma valid_data1907 : data1907.Valid src1907 dst1907 Finset.univ := by decide +kernel

def src1908 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,26,38,8,18,28,38]
def dst1908 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1908_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1908_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1908_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1908_3 : CycleData E W := ⟨3,![5,4,12,13,6],![2,8,5,26,14]⟩
def cycle1908_4 : CycleData E W := ⟨1,![7,21,14],![14,18,28]⟩
def cycle1908_5 : CycleData E W := ⟨4,![8,20,23,18,17,9],![3,18,8,38,26,16]⟩
def data1908 : PartitionData E W := ⟨6,![cycle1908_0,cycle1908_1,cycle1908_2,cycle1908_3,cycle1908_4,cycle1908_5]⟩
lemma valid_data1908 : data1908.Valid src1908 dst1908 Finset.univ := by decide +kernel

def src1909 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,26,38,8,18,38,28]
def dst1909 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1909_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1909_1 : CycleData E W := ⟨3,![2,1,19,21,8],![3,4,6,38,18]⟩
def cycle1909_2 : CycleData E W := ⟨2,![3,12,17,9],![3,5,26,16]⟩
def cycle1909_3 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1909_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle1909_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1909 : PartitionData E W := ⟨6,![cycle1909_0,cycle1909_1,cycle1909_2,cycle1909_3,cycle1909_4,cycle1909_5]⟩
lemma valid_data1909 : data1909.Valid src1909 dst1909 Finset.univ := by decide +kernel

def src1910 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,26,38,8,28,18,38]
def dst1910 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1910_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1910_1 : CycleData E W := ⟨3,![2,1,19,22,8],![3,4,6,38,18]⟩
def cycle1910_2 : CycleData E W := ⟨2,![3,12,17,9],![3,5,26,16]⟩
def cycle1910_3 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle1910_4 : CycleData E W := ⟨3,![5,23,18,13,6],![2,8,38,26,14]⟩
def cycle1910_5 : CycleData E W := ⟨1,![7,21,14],![14,18,28]⟩
def data1910 : PartitionData E W := ⟨6,![cycle1910_0,cycle1910_1,cycle1910_2,cycle1910_3,cycle1910_4,cycle1910_5]⟩
lemma valid_data1910 : data1910.Valid src1910 dst1910 Finset.univ := by decide +kernel

def src1911 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,38,26,8,18,28,38]
def dst1911 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1911_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1911_1 : CycleData E W := ⟨2,![1,19,12,11],![4,6,26,5]⟩
def cycle1911_2 : CycleData E W := ⟨2,![2,15,21,8],![3,4,28,18]⟩
def cycle1911_3 : CycleData E W := ⟨3,![3,4,23,17,9],![3,5,8,38,16]⟩
def cycle1911_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle1911_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1911 : PartitionData E W := ⟨6,![cycle1911_0,cycle1911_1,cycle1911_2,cycle1911_3,cycle1911_4,cycle1911_5]⟩
lemma valid_data1911 : data1911.Valid src1911 dst1911 Finset.univ := by decide +kernel

def src1912 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,38,26,8,18,38,28]
def dst1912 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1912_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1912_1 : CycleData E W := ⟨3,![2,1,19,12,3],![3,4,6,26,5]⟩
def cycle1912_2 : CycleData E W := ⟨2,![11,4,23,15],![4,5,8,28]⟩
def cycle1912_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle1912_4 : CycleData E W := ⟨2,![8,21,17,9],![3,18,38,16]⟩
def cycle1912_5 : CycleData E W := ⟨2,![13,18,22,14],![14,26,38,28]⟩
def data1912 : PartitionData E W := ⟨6,![cycle1912_0,cycle1912_1,cycle1912_2,cycle1912_3,cycle1912_4,cycle1912_5]⟩
lemma valid_data1912 : data1912.Valid src1912 dst1912 Finset.univ := by decide +kernel

def src1913 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,16,38,26,8,28,18,38]
def dst1913 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1913_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1913_1 : CycleData E W := ⟨3,![2,1,19,12,3],![3,4,6,26,5]⟩
def cycle1913_2 : CycleData E W := ⟨2,![11,4,20,15],![4,5,8,28]⟩
def cycle1913_3 : CycleData E W := ⟨3,![5,23,18,13,6],![2,8,38,26,14]⟩
def cycle1913_4 : CycleData E W := ⟨1,![7,21,14],![14,18,28]⟩
def cycle1913_5 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def data1913 : PartitionData E W := ⟨6,![cycle1913_0,cycle1913_1,cycle1913_2,cycle1913_3,cycle1913_4,cycle1913_5]⟩
lemma valid_data1913 : data1913.Valid src1913 dst1913 Finset.univ := by decide +kernel

def src1914 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,26,16,38,8,18,28,38]
def dst1914 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1914_0 : CycleData E W := ⟨3,![0,16,12,4,5],![2,6,26,5,8]⟩
def cycle1914_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1914_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1914_3 : CycleData E W := ⟨2,![6,13,17,10],![2,14,26,16]⟩
def cycle1914_4 : CycleData E W := ⟨1,![7,21,14],![14,18,28]⟩
def cycle1914_5 : CycleData E W := ⟨3,![8,20,23,18,9],![3,18,8,38,16]⟩
def data1914 : PartitionData E W := ⟨6,![cycle1914_0,cycle1914_1,cycle1914_2,cycle1914_3,cycle1914_4,cycle1914_5]⟩
lemma valid_data1914 : data1914.Valid src1914 dst1914 Finset.univ := by decide +kernel

def src1915 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,26,16,38,8,18,38,28]
def dst1915 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1915_0 : CycleData E W := ⟨3,![0,16,12,4,5],![2,6,26,5,8]⟩
def cycle1915_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1915_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1915_3 : CycleData E W := ⟨2,![6,13,17,10],![2,14,26,16]⟩
def cycle1915_4 : CycleData E W := ⟨2,![20,7,14,23],![8,18,14,28]⟩
def cycle1915_5 : CycleData E W := ⟨2,![8,21,18,9],![3,18,38,16]⟩
def data1915 : PartitionData E W := ⟨6,![cycle1915_0,cycle1915_1,cycle1915_2,cycle1915_3,cycle1915_4,cycle1915_5]⟩
lemma valid_data1915 : data1915.Valid src1915 dst1915 Finset.univ := by decide +kernel

def src1916 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,5,26,14,28,6,26,16,38,8,28,18,38]
def dst1916 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,5,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1916_0 : CycleData E W := ⟨3,![0,16,12,4,5],![2,6,26,5,8]⟩
def cycle1916_1 : CycleData E W := ⟨3,![1,19,23,20,15],![4,6,38,8,28]⟩
def cycle1916_2 : CycleData E W := ⟨1,![2,11,3],![3,4,5]⟩
def cycle1916_3 : CycleData E W := ⟨2,![6,13,17,10],![2,14,26,16]⟩
def cycle1916_4 : CycleData E W := ⟨1,![7,21,14],![14,18,28]⟩
def cycle1916_5 : CycleData E W := ⟨2,![8,22,18,9],![3,18,38,16]⟩
def data1916 : PartitionData E W := ⟨6,![cycle1916_0,cycle1916_1,cycle1916_2,cycle1916_3,cycle1916_4,cycle1916_5]⟩
lemma valid_data1916 : data1916.Valid src1916 dst1916 Finset.univ := by decide +kernel

def src1917 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,26,38,8,18,28,38]
def dst1917 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,26,38,6,18,28,38,8]
def cycle1917_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1917_1 : CycleData E W := ⟨3,![1,19,18,12,11],![4,6,38,26,14]⟩
def cycle1917_2 : CycleData E W := ⟨2,![2,15,21,8],![3,4,28,18]⟩
def cycle1917_3 : CycleData E W := ⟨2,![3,13,17,9],![3,5,26,16]⟩
def cycle1917_4 : CycleData E W := ⟨2,![4,23,22,14],![5,8,38,28]⟩
def cycle1917_5 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def data1917 : PartitionData E W := ⟨6,![cycle1917_0,cycle1917_1,cycle1917_2,cycle1917_3,cycle1917_4,cycle1917_5]⟩
lemma valid_data1917 : data1917.Valid src1917 dst1917 Finset.univ := by decide +kernel

def src1918 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,26,38,8,18,38,28]
def dst1918 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,26,38,6,18,38,28,8]
def cycle1918_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1918_1 : CycleData E W := ⟨3,![1,19,18,12,11],![4,6,38,26,14]⟩
def cycle1918_2 : CycleData E W := ⟨3,![2,15,22,21,8],![3,4,28,38,18]⟩
def cycle1918_3 : CycleData E W := ⟨2,![3,13,17,9],![3,5,26,16]⟩
def cycle1918_4 : CycleData E W := ⟨1,![4,23,14],![5,8,28]⟩
def cycle1918_5 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def data1918 : PartitionData E W := ⟨6,![cycle1918_0,cycle1918_1,cycle1918_2,cycle1918_3,cycle1918_4,cycle1918_5]⟩
lemma valid_data1918 : data1918.Valid src1918 dst1918 Finset.univ := by decide +kernel

def src1919 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,26,38,8,28,18,38]
def dst1919 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,26,38,6,28,18,38,8]
def cycle1919_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle1919_1 : CycleData E W := ⟨2,![2,15,21,8],![3,4,28,18]⟩
def cycle1919_2 : CycleData E W := ⟨2,![3,13,17,9],![3,5,26,16]⟩
def cycle1919_3 : CycleData E W := ⟨1,![4,20,14],![5,8,28]⟩
def cycle1919_4 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle1919_5 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def data1919 : PartitionData E W := ⟨6,![cycle1919_0,cycle1919_1,cycle1919_2,cycle1919_3,cycle1919_4,cycle1919_5]⟩
lemma valid_data1919 : data1919.Valid src1919 dst1919 Finset.univ := by decide +kernel

def src1920 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,8,18,28,38]
def dst1920 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,6,18,28,38,8]
def cycle1920_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1920_1 : CycleData E W := ⟨2,![1,19,12,11],![4,6,26,14]⟩
def cycle1920_2 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle1920_3 : CycleData E W := ⟨2,![4,23,18,13],![5,8,38,26]⟩
def cycle1920_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle1920_5 : CycleData E W := ⟨3,![8,21,22,17,9],![3,18,28,38,16]⟩
def data1920 : PartitionData E W := ⟨6,![cycle1920_0,cycle1920_1,cycle1920_2,cycle1920_3,cycle1920_4,cycle1920_5]⟩
lemma valid_data1920 : data1920.Valid src1920 dst1920 Finset.univ := by decide +kernel

def src1921 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,8,18,38,28]
def dst1921 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,6,18,38,28,8]
def cycle1921_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle1921_1 : CycleData E W := ⟨2,![1,19,12,11],![4,6,26,14]⟩
def cycle1921_2 : CycleData E W := ⟨2,![2,15,14,3],![3,4,28,5]⟩
def cycle1921_3 : CycleData E W := ⟨3,![4,23,22,18,13],![5,8,28,38,26]⟩
def cycle1921_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle1921_5 : CycleData E W := ⟨2,![8,21,17,9],![3,18,38,16]⟩
def data1921 : PartitionData E W := ⟨6,![cycle1921_0,cycle1921_1,cycle1921_2,cycle1921_3,cycle1921_4,cycle1921_5]⟩
lemma valid_data1921 : data1921.Valid src1921 dst1921 Finset.univ := by decide +kernel

def src1922 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,16,38,26,8,28,18,38]
def dst1922 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,16,38,26,6,28,18,38,8]
def cycle1922_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle1922_1 : CycleData E W := ⟨2,![2,15,21,8],![3,4,28,18]⟩
def cycle1922_2 : CycleData E W := ⟨3,![3,13,19,16,9],![3,5,26,6,16]⟩
def cycle1922_3 : CycleData E W := ⟨1,![4,20,14],![5,8,28]⟩
def cycle1922_4 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle1922_5 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def data1922 : PartitionData E W := ⟨6,![cycle1922_0,cycle1922_1,cycle1922_2,cycle1922_3,cycle1922_4,cycle1922_5]⟩
lemma valid_data1922 : data1922.Valid src1922 dst1922 Finset.univ := by decide +kernel

def src1923 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,16,38,8,18,28,38]
def dst1923 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,16,38,6,18,28,38,8]
def cycle1923_0 : CycleData E W := ⟨2,![0,16,12,6],![2,6,26,14]⟩
def cycle1923_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1923_2 : CycleData E W := ⟨2,![2,11,7,8],![3,4,14,18]⟩
def cycle1923_3 : CycleData E W := ⟨2,![3,13,17,9],![3,5,26,16]⟩
def cycle1923_4 : CycleData E W := ⟨2,![4,20,21,14],![5,8,18,28]⟩
def cycle1923_5 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def data1923 : PartitionData E W := ⟨6,![cycle1923_0,cycle1923_1,cycle1923_2,cycle1923_3,cycle1923_4,cycle1923_5]⟩
lemma valid_data1923 : data1923.Valid src1923 dst1923 Finset.univ := by decide +kernel

def src1924 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,16,38,8,18,38,28]
def dst1924 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,16,38,6,18,38,28,8]
def cycle1924_0 : CycleData E W := ⟨2,![0,16,12,6],![2,6,26,14]⟩
def cycle1924_1 : CycleData E W := ⟨2,![1,19,22,15],![4,6,38,28]⟩
def cycle1924_2 : CycleData E W := ⟨2,![2,11,7,8],![3,4,14,18]⟩
def cycle1924_3 : CycleData E W := ⟨2,![3,13,17,9],![3,5,26,16]⟩
def cycle1924_4 : CycleData E W := ⟨1,![4,23,14],![5,8,28]⟩
def cycle1924_5 : CycleData E W := ⟨3,![5,20,21,18,10],![2,8,18,38,16]⟩
def data1924 : PartitionData E W := ⟨6,![cycle1924_0,cycle1924_1,cycle1924_2,cycle1924_3,cycle1924_4,cycle1924_5]⟩
lemma valid_data1924 : data1924.Valid src1924 dst1924 Finset.univ := by decide +kernel

def src1925 : E → W := ![2,6,4,3,5,8,2,14,18,3,16,4,14,26,5,28,6,26,16,38,8,28,18,38]
def dst1925 : E → W := ![6,4,3,5,8,2,14,18,3,16,2,14,26,5,28,4,26,16,38,6,28,18,38,8]
def cycle1925_0 : CycleData E W := ⟨2,![0,1,11,6],![2,6,4,14]⟩
def cycle1925_1 : CycleData E W := ⟨2,![2,15,21,8],![3,4,28,18]⟩
def cycle1925_2 : CycleData E W := ⟨2,![3,13,17,9],![3,5,26,16]⟩
def cycle1925_3 : CycleData E W := ⟨1,![4,20,14],![5,8,28]⟩
def cycle1925_4 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle1925_5 : CycleData E W := ⟨3,![16,12,7,22,19],![6,26,14,18,38]⟩
def data1925 : PartitionData E W := ⟨6,![cycle1925_0,cycle1925_1,cycle1925_2,cycle1925_3,cycle1925_4,cycle1925_5]⟩
lemma valid_data1925 : data1925.Valid src1925 dst1925 Finset.univ := by decide +kernel

def src1926 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,16,26,38,8,18,28,38]
def dst1926 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,16,26,38,6,18,28,38,8]
def cycle1926_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,3]⟩
def cycle1926_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle1926_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle1926_3 : CycleData E W := ⟨3,![5,4,15,14,10],![2,8,4,26,14]⟩
def cycle1926_4 : CycleData E W := ⟨3,![20,8,17,18,23],![8,18,16,26,38]⟩
def cycle1926_5 : CycleData E W := ⟨1,![9,21,13],![14,18,28]⟩
def data1926 : PartitionData E W := ⟨6,![cycle1926_0,cycle1926_1,cycle1926_2,cycle1926_3,cycle1926_4,cycle1926_5]⟩
lemma valid_data1926 : data1926.Valid src1926 dst1926 Finset.univ := by decide +kernel

def src1927 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,16,26,38,8,18,38,28]
def dst1927 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,16,26,38,6,18,38,28,8]
def cycle1927_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1927_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1927_2 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,5]⟩
def cycle1927_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1927_4 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1927_5 : CycleData E W := ⟨2,![13,22,18,14],![14,28,38,26]⟩
def data1927 : PartitionData E W := ⟨6,![cycle1927_0,cycle1927_1,cycle1927_2,cycle1927_3,cycle1927_4,cycle1927_5]⟩
lemma valid_data1927 : data1927.Valid src1927 dst1927 Finset.univ := by decide +kernel

def src1928 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,16,26,38,8,28,18,38]
def dst1928 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,16,26,38,6,28,18,38,8]
def cycle1928_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1928_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1928_2 : CycleData E W := ⟨2,![4,20,12,11],![4,8,28,5]⟩
def cycle1928_3 : CycleData E W := ⟨3,![5,23,18,14,10],![2,8,38,26,14]⟩
def cycle1928_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1928_5 : CycleData E W := ⟨1,![9,21,13],![14,18,28]⟩
def data1928 : PartitionData E W := ⟨6,![cycle1928_0,cycle1928_1,cycle1928_2,cycle1928_3,cycle1928_4,cycle1928_5]⟩
lemma valid_data1928 : data1928.Valid src1928 dst1928 Finset.univ := by decide +kernel

def src1929 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,16,38,26,8,18,28,38]
def dst1929 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,16,38,26,6,18,28,38,8]
def cycle1929_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,3]⟩
def cycle1929_1 : CycleData E W := ⟨3,![1,19,14,13,12],![5,6,26,14,28]⟩
def cycle1929_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle1929_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1929_4 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1929_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data1929 : PartitionData E W := ⟨6,![cycle1929_0,cycle1929_1,cycle1929_2,cycle1929_3,cycle1929_4,cycle1929_5]⟩
lemma valid_data1929 : data1929.Valid src1929 dst1929 Finset.univ := by decide +kernel

def src1930 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,16,38,26,8,18,38,28]
def dst1930 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,16,38,26,6,18,38,28,8]
def cycle1930_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1930_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1930_2 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,5]⟩
def cycle1930_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1930_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1930_5 : CycleData E W := ⟨2,![13,22,18,14],![14,28,38,26]⟩
def data1930 : PartitionData E W := ⟨6,![cycle1930_0,cycle1930_1,cycle1930_2,cycle1930_3,cycle1930_4,cycle1930_5]⟩
lemma valid_data1930 : data1930.Valid src1930 dst1930 Finset.univ := by decide +kernel

def src1931 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,16,38,26,8,28,18,38]
def dst1931 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,16,38,26,6,28,18,38,8]
def cycle1931_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1931_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1931_2 : CycleData E W := ⟨2,![4,20,12,11],![4,8,28,5]⟩
def cycle1931_3 : CycleData E W := ⟨3,![5,23,18,14,10],![2,8,38,26,14]⟩
def cycle1931_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1931_5 : CycleData E W := ⟨1,![9,21,13],![14,18,28]⟩
def data1931 : PartitionData E W := ⟨6,![cycle1931_0,cycle1931_1,cycle1931_2,cycle1931_3,cycle1931_4,cycle1931_5]⟩
lemma valid_data1931 : data1931.Valid src1931 dst1931 Finset.univ := by decide +kernel

def src1932 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,26,16,38,8,18,28,38]
def dst1932 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,26,16,38,6,18,28,38,8]
def cycle1932_0 : CycleData E W := ⟨2,![0,16,14,10],![2,6,26,14]⟩
def cycle1932_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle1932_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle1932_3 : CycleData E W := ⟨4,![5,4,15,17,7,6],![2,8,4,26,16,3]⟩
def cycle1932_4 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1932_5 : CycleData E W := ⟨1,![9,21,13],![14,18,28]⟩
def data1932 : PartitionData E W := ⟨6,![cycle1932_0,cycle1932_1,cycle1932_2,cycle1932_3,cycle1932_4,cycle1932_5]⟩
lemma valid_data1932 : data1932.Valid src1932 dst1932 Finset.univ := by decide +kernel

def src1933 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,26,16,38,8,18,38,28]
def dst1933 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,26,16,38,6,18,38,28,8]
def cycle1933_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1933_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1933_2 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,5]⟩
def cycle1933_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1933_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1933_5 : CycleData E W := ⟨3,![16,14,13,22,19],![6,26,14,28,38]⟩
def data1933 : PartitionData E W := ⟨6,![cycle1933_0,cycle1933_1,cycle1933_2,cycle1933_3,cycle1933_4,cycle1933_5]⟩
lemma valid_data1933 : data1933.Valid src1933 dst1933 Finset.univ := by decide +kernel

def src1934 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,5,28,14,26,6,26,16,38,8,28,18,38]
def dst1934 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,5,28,14,26,4,26,16,38,6,28,18,38,8]
def cycle1934_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1934_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1934_2 : CycleData E W := ⟨2,![4,20,12,11],![4,8,28,5]⟩
def cycle1934_3 : CycleData E W := ⟨4,![5,23,19,16,14,10],![2,8,38,6,26,14]⟩
def cycle1934_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1934_5 : CycleData E W := ⟨1,![9,21,13],![14,18,28]⟩
def data1934 : PartitionData E W := ⟨6,![cycle1934_0,cycle1934_1,cycle1934_2,cycle1934_3,cycle1934_4,cycle1934_5]⟩
lemma valid_data1934 : data1934.Valid src1934 dst1934 Finset.univ := by decide +kernel

def src1935 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,16,26,38,8,18,28,38]
def dst1935 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,16,26,38,6,18,28,38,8]
def cycle1935_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1935_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1935_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1935_3 : CycleData E W := ⟨3,![16,8,20,23,19],![6,16,18,8,38]⟩
def cycle1935_4 : CycleData E W := ⟨2,![12,9,21,13],![5,14,18,28]⟩
def cycle1935_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1935 : PartitionData E W := ⟨6,![cycle1935_0,cycle1935_1,cycle1935_2,cycle1935_3,cycle1935_4,cycle1935_5]⟩
lemma valid_data1935 : data1935.Valid src1935 dst1935 Finset.univ := by decide +kernel

def src1936 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,16,26,38,8,18,38,28]
def dst1936 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,16,26,38,6,18,38,28,8]
def cycle1936_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1936_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1936_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1936_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1936_4 : CycleData E W := ⟨3,![12,9,20,23,13],![5,14,18,8,28]⟩
def cycle1936_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1936 : PartitionData E W := ⟨6,![cycle1936_0,cycle1936_1,cycle1936_2,cycle1936_3,cycle1936_4,cycle1936_5]⟩
lemma valid_data1936 : data1936.Valid src1936 dst1936 Finset.univ := by decide +kernel

def src1937 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,16,26,38,8,28,18,38]
def dst1937 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,16,26,38,6,28,18,38,8]
def cycle1937_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1937_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1937_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1937_3 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1937_4 : CycleData E W := ⟨2,![12,9,21,13],![5,14,18,28]⟩
def cycle1937_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1937 : PartitionData E W := ⟨6,![cycle1937_0,cycle1937_1,cycle1937_2,cycle1937_3,cycle1937_4,cycle1937_5]⟩
lemma valid_data1937 : data1937.Valid src1937 dst1937 Finset.univ := by decide +kernel

def src1938 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,16,38,26,8,18,28,38]
def dst1938 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,16,38,26,6,18,28,38,8]
def cycle1938_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1938_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1938_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1938_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle1938_4 : CycleData E W := ⟨2,![12,9,21,13],![5,14,18,28]⟩
def cycle1938_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1938 : PartitionData E W := ⟨6,![cycle1938_0,cycle1938_1,cycle1938_2,cycle1938_3,cycle1938_4,cycle1938_5]⟩
lemma valid_data1938 : data1938.Valid src1938 dst1938 Finset.univ := by decide +kernel

def src1939 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,16,38,26,8,18,38,28]
def dst1939 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,16,38,26,6,18,38,28,8]
def cycle1939_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1939_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1939_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1939_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1939_4 : CycleData E W := ⟨3,![12,9,20,23,13],![5,14,18,8,28]⟩
def cycle1939_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1939 : PartitionData E W := ⟨6,![cycle1939_0,cycle1939_1,cycle1939_2,cycle1939_3,cycle1939_4,cycle1939_5]⟩
lemma valid_data1939 : data1939.Valid src1939 dst1939 Finset.univ := by decide +kernel

def src1940 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,16,38,26,8,28,18,38]
def dst1940 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,16,38,26,6,28,18,38,8]
def cycle1940_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1940_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1940_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1940_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1940_4 : CycleData E W := ⟨2,![12,9,21,13],![5,14,18,28]⟩
def cycle1940_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1940 : PartitionData E W := ⟨6,![cycle1940_0,cycle1940_1,cycle1940_2,cycle1940_3,cycle1940_4,cycle1940_5]⟩
lemma valid_data1940 : data1940.Valid src1940 dst1940 Finset.univ := by decide +kernel

def src1941 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,26,16,38,8,18,28,38]
def dst1941 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,26,16,38,6,18,28,38,8]
def cycle1941_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1941_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1941_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1941_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1941_4 : CycleData E W := ⟨2,![12,9,21,13],![5,14,18,28]⟩
def cycle1941_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1941 : PartitionData E W := ⟨6,![cycle1941_0,cycle1941_1,cycle1941_2,cycle1941_3,cycle1941_4,cycle1941_5]⟩
lemma valid_data1941 : data1941.Valid src1941 dst1941 Finset.univ := by decide +kernel

def src1942 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,26,16,38,8,18,38,28]
def dst1942 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,26,16,38,6,18,38,28,8]
def cycle1942_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1942_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1942_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1942_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1942_4 : CycleData E W := ⟨3,![12,9,20,23,13],![5,14,18,8,28]⟩
def cycle1942_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1942 : PartitionData E W := ⟨6,![cycle1942_0,cycle1942_1,cycle1942_2,cycle1942_3,cycle1942_4,cycle1942_5]⟩
lemma valid_data1942 : data1942.Valid src1942 dst1942 Finset.univ := by decide +kernel

def src1943 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,5,28,26,6,26,16,38,8,28,18,38]
def dst1943 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,5,28,26,4,26,16,38,6,28,18,38,8]
def cycle1943_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1943_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1943_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1943_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1943_4 : CycleData E W := ⟨2,![12,9,21,13],![5,14,18,28]⟩
def cycle1943_5 : CycleData E W := ⟨3,![16,14,20,23,19],![6,26,28,8,38]⟩
def data1943 : PartitionData E W := ⟨6,![cycle1943_0,cycle1943_1,cycle1943_2,cycle1943_3,cycle1943_4,cycle1943_5]⟩
lemma valid_data1943 : data1943.Valid src1943 dst1943 Finset.univ := by decide +kernel

def src1944 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,16,26,38,8,18,28,38]
def dst1944 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,16,26,38,6,18,28,38,8]
def cycle1944_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1944_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1944_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1944_3 : CycleData E W := ⟨3,![16,8,20,23,19],![6,16,18,8,38]⟩
def cycle1944_4 : CycleData E W := ⟨1,![9,21,12],![14,18,28]⟩
def cycle1944_5 : CycleData E W := ⟨2,![13,22,18,14],![5,28,38,26]⟩
def data1944 : PartitionData E W := ⟨6,![cycle1944_0,cycle1944_1,cycle1944_2,cycle1944_3,cycle1944_4,cycle1944_5]⟩
lemma valid_data1944 : data1944.Valid src1944 dst1944 Finset.univ := by decide +kernel

def src1945 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,16,26,38,8,18,38,28]
def dst1945 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,16,26,38,6,18,38,28,8]
def cycle1945_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1945_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1945_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1945_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1945_4 : CycleData E W := ⟨2,![20,9,12,23],![8,18,14,28]⟩
def cycle1945_5 : CycleData E W := ⟨2,![13,22,18,14],![5,28,38,26]⟩
def data1945 : PartitionData E W := ⟨6,![cycle1945_0,cycle1945_1,cycle1945_2,cycle1945_3,cycle1945_4,cycle1945_5]⟩
lemma valid_data1945 : data1945.Valid src1945 dst1945 Finset.univ := by decide +kernel

def src1946 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,16,26,38,8,28,18,38]
def dst1946 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,16,26,38,6,28,18,38,8]
def cycle1946_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1946_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1946_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1946_3 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1946_4 : CycleData E W := ⟨1,![9,21,12],![14,18,28]⟩
def cycle1946_5 : CycleData E W := ⟨3,![13,20,23,18,14],![5,28,8,38,26]⟩
def data1946 : PartitionData E W := ⟨6,![cycle1946_0,cycle1946_1,cycle1946_2,cycle1946_3,cycle1946_4,cycle1946_5]⟩
lemma valid_data1946 : data1946.Valid src1946 dst1946 Finset.univ := by decide +kernel

def src1947 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,16,38,26,8,18,28,38]
def dst1947 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,16,38,26,6,18,28,38,8]
def cycle1947_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1947_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1947_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1947_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle1947_4 : CycleData E W := ⟨1,![9,21,12],![14,18,28]⟩
def cycle1947_5 : CycleData E W := ⟨2,![13,22,18,14],![5,28,38,26]⟩
def data1947 : PartitionData E W := ⟨6,![cycle1947_0,cycle1947_1,cycle1947_2,cycle1947_3,cycle1947_4,cycle1947_5]⟩
lemma valid_data1947 : data1947.Valid src1947 dst1947 Finset.univ := by decide +kernel

def src1948 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,16,38,26,8,18,38,28]
def dst1948 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,16,38,26,6,18,38,28,8]
def cycle1948_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1948_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1948_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1948_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1948_4 : CycleData E W := ⟨2,![20,9,12,23],![8,18,14,28]⟩
def cycle1948_5 : CycleData E W := ⟨2,![13,22,18,14],![5,28,38,26]⟩
def data1948 : PartitionData E W := ⟨6,![cycle1948_0,cycle1948_1,cycle1948_2,cycle1948_3,cycle1948_4,cycle1948_5]⟩
lemma valid_data1948 : data1948.Valid src1948 dst1948 Finset.univ := by decide +kernel

def src1949 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,16,38,26,8,28,18,38]
def dst1949 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,16,38,26,6,28,18,38,8]
def cycle1949_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1949_1 : CycleData E W := ⟨3,![3,15,19,16,7],![3,4,26,6,16]⟩
def cycle1949_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1949_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1949_4 : CycleData E W := ⟨1,![9,21,12],![14,18,28]⟩
def cycle1949_5 : CycleData E W := ⟨3,![13,20,23,18,14],![5,28,8,38,26]⟩
def data1949 : PartitionData E W := ⟨6,![cycle1949_0,cycle1949_1,cycle1949_2,cycle1949_3,cycle1949_4,cycle1949_5]⟩
lemma valid_data1949 : data1949.Valid src1949 dst1949 Finset.univ := by decide +kernel

def src1950 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,26,16,38,8,18,28,38]
def dst1950 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,26,16,38,6,18,28,38,8]
def cycle1950_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1950_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1950_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1950_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1950_4 : CycleData E W := ⟨1,![9,21,12],![14,18,28]⟩
def cycle1950_5 : CycleData E W := ⟨3,![13,22,19,16,14],![5,28,38,6,26]⟩
def data1950 : PartitionData E W := ⟨6,![cycle1950_0,cycle1950_1,cycle1950_2,cycle1950_3,cycle1950_4,cycle1950_5]⟩
lemma valid_data1950 : data1950.Valid src1950 dst1950 Finset.univ := by decide +kernel

def src1951 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,26,16,38,8,18,38,28]
def dst1951 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,26,16,38,6,18,38,28,8]
def cycle1951_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1951_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1951_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1951_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1951_4 : CycleData E W := ⟨2,![20,9,12,23],![8,18,14,28]⟩
def cycle1951_5 : CycleData E W := ⟨3,![13,22,19,16,14],![5,28,38,6,26]⟩
def data1951 : PartitionData E W := ⟨6,![cycle1951_0,cycle1951_1,cycle1951_2,cycle1951_3,cycle1951_4,cycle1951_5]⟩
lemma valid_data1951 : data1951.Valid src1951 dst1951 Finset.univ := by decide +kernel

def src1952 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,14,28,5,26,6,26,16,38,8,28,18,38]
def dst1952 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,14,28,5,26,4,26,16,38,6,28,18,38,8]
def cycle1952_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1952_1 : CycleData E W := ⟨2,![3,15,17,7],![3,4,26,16]⟩
def cycle1952_2 : CycleData E W := ⟨2,![5,4,11,10],![2,8,4,14]⟩
def cycle1952_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1952_4 : CycleData E W := ⟨1,![9,21,12],![14,18,28]⟩
def cycle1952_5 : CycleData E W := ⟨4,![13,20,23,19,16,14],![5,28,8,38,6,26]⟩
def data1952 : PartitionData E W := ⟨6,![cycle1952_0,cycle1952_1,cycle1952_2,cycle1952_3,cycle1952_4,cycle1952_5]⟩
lemma valid_data1952 : data1952.Valid src1952 dst1952 Finset.univ := by decide +kernel

def src1953 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,16,26,38,8,18,28,38]
def dst1953 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,16,26,38,6,18,28,38,8]
def cycle1953_0 : CycleData E W := ⟨10,![5,20,8,7,3,15,14,1,19,18,12,10],![2,8,18,16,3,4,28,5,6,38,26,14]⟩
def cycle1953_1 : CycleData E W := ⟨10,![0,16,17,11,4,23,22,21,9,13,2,6],![2,6,16,26,4,8,38,28,18,14,5,3]⟩
def data1953 : PartitionData E W := ⟨2,![cycle1953_0,cycle1953_1]⟩
lemma valid_data1953 : data1953.Valid src1953 dst1953 Finset.univ := by decide +kernel

def src1954 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,16,26,38,8,18,38,28]
def dst1954 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,16,26,38,6,18,38,28,8]
def cycle1954_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1954_1 : CycleData E W := ⟨2,![3,11,17,7],![3,4,26,16]⟩
def cycle1954_2 : CycleData E W := ⟨1,![4,23,15],![4,8,28]⟩
def cycle1954_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1954_4 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1954_5 : CycleData E W := ⟨3,![13,12,18,22,14],![5,14,26,38,28]⟩
def data1954 : PartitionData E W := ⟨6,![cycle1954_0,cycle1954_1,cycle1954_2,cycle1954_3,cycle1954_4,cycle1954_5]⟩
lemma valid_data1954 : data1954.Valid src1954 dst1954 Finset.univ := by decide +kernel

def src1955 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,16,26,38,8,28,18,38]
def dst1955 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,16,26,38,6,28,18,38,8]
def cycle1955_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1955_1 : CycleData E W := ⟨2,![3,11,17,7],![3,4,26,16]⟩
def cycle1955_2 : CycleData E W := ⟨1,![4,20,15],![4,8,28]⟩
def cycle1955_3 : CycleData E W := ⟨3,![5,23,18,12,10],![2,8,38,26,14]⟩
def cycle1955_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1955_5 : CycleData E W := ⟨2,![13,9,21,14],![5,14,18,28]⟩
def data1955 : PartitionData E W := ⟨6,![cycle1955_0,cycle1955_1,cycle1955_2,cycle1955_3,cycle1955_4,cycle1955_5]⟩
lemma valid_data1955 : data1955.Valid src1955 dst1955 Finset.univ := by decide +kernel

def src1956 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,16,38,26,8,18,28,38]
def dst1956 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,16,38,26,6,18,28,38,8]
def cycle1956_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,3]⟩
def cycle1956_1 : CycleData E W := ⟨2,![1,19,12,13],![5,6,26,14]⟩
def cycle1956_2 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle1956_3 : CycleData E W := ⟨2,![4,23,18,11],![4,8,38,26]⟩
def cycle1956_4 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1956_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data1956 : PartitionData E W := ⟨6,![cycle1956_0,cycle1956_1,cycle1956_2,cycle1956_3,cycle1956_4,cycle1956_5]⟩
lemma valid_data1956 : data1956.Valid src1956 dst1956 Finset.univ := by decide +kernel

def src1957 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,16,38,26,8,18,38,28]
def dst1957 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,16,38,26,6,18,38,28,8]
def cycle1957_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1957_1 : CycleData E W := ⟨3,![3,11,19,16,7],![3,4,26,6,16]⟩
def cycle1957_2 : CycleData E W := ⟨1,![4,23,15],![4,8,28]⟩
def cycle1957_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1957_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1957_5 : CycleData E W := ⟨3,![13,12,18,22,14],![5,14,26,38,28]⟩
def data1957 : PartitionData E W := ⟨6,![cycle1957_0,cycle1957_1,cycle1957_2,cycle1957_3,cycle1957_4,cycle1957_5]⟩
lemma valid_data1957 : data1957.Valid src1957 dst1957 Finset.univ := by decide +kernel

def src1958 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,16,38,26,8,28,18,38]
def dst1958 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,16,38,26,6,28,18,38,8]
def cycle1958_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1958_1 : CycleData E W := ⟨3,![3,11,19,16,7],![3,4,26,6,16]⟩
def cycle1958_2 : CycleData E W := ⟨1,![4,20,15],![4,8,28]⟩
def cycle1958_3 : CycleData E W := ⟨3,![5,23,18,12,10],![2,8,38,26,14]⟩
def cycle1958_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1958_5 : CycleData E W := ⟨2,![13,9,21,14],![5,14,18,28]⟩
def data1958 : PartitionData E W := ⟨6,![cycle1958_0,cycle1958_1,cycle1958_2,cycle1958_3,cycle1958_4,cycle1958_5]⟩
lemma valid_data1958 : data1958.Valid src1958 dst1958 Finset.univ := by decide +kernel

def src1959 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,26,16,38,8,18,28,38]
def dst1959 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,26,16,38,6,18,28,38,8]
def cycle1959_0 : CycleData E W := ⟨10,![0,19,18,7,2,14,15,11,12,9,20,5],![2,6,38,16,3,5,28,4,26,14,18,8]⟩
def cycle1959_1 : CycleData E W := ⟨10,![6,3,4,23,22,21,8,17,16,1,13,10],![2,3,4,8,38,28,18,16,26,6,5,14]⟩
def data1959 : PartitionData E W := ⟨2,![cycle1959_0,cycle1959_1]⟩
lemma valid_data1959 : data1959.Valid src1959 dst1959 Finset.univ := by decide +kernel

def src1960 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,26,16,38,8,18,38,28]
def dst1960 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,26,16,38,6,18,38,28,8]
def cycle1960_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1960_1 : CycleData E W := ⟨2,![3,11,17,7],![3,4,26,16]⟩
def cycle1960_2 : CycleData E W := ⟨1,![4,23,15],![4,8,28]⟩
def cycle1960_3 : CycleData E W := ⟨2,![5,20,9,10],![2,8,18,14]⟩
def cycle1960_4 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1960_5 : CycleData E W := ⟨4,![13,12,16,19,22,14],![5,14,26,6,38,28]⟩
def data1960 : PartitionData E W := ⟨6,![cycle1960_0,cycle1960_1,cycle1960_2,cycle1960_3,cycle1960_4,cycle1960_5]⟩
lemma valid_data1960 : data1960.Valid src1960 dst1960 Finset.univ := by decide +kernel

def src1961 : E → W := ![2,6,5,3,4,8,2,3,16,18,14,4,26,14,5,28,6,26,16,38,8,28,18,38]
def dst1961 : E → W := ![6,5,3,4,8,2,3,16,18,14,2,26,14,5,28,4,26,16,38,6,28,18,38,8]
def cycle1961_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1961_1 : CycleData E W := ⟨2,![3,11,17,7],![3,4,26,16]⟩
def cycle1961_2 : CycleData E W := ⟨1,![4,20,15],![4,8,28]⟩
def cycle1961_3 : CycleData E W := ⟨4,![5,23,19,16,12,10],![2,8,38,6,26,14]⟩
def cycle1961_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1961_5 : CycleData E W := ⟨2,![13,9,21,14],![5,14,18,28]⟩
def data1961 : PartitionData E W := ⟨6,![cycle1961_0,cycle1961_1,cycle1961_2,cycle1961_3,cycle1961_4,cycle1961_5]⟩
lemma valid_data1961 : data1961.Valid src1961 dst1961 Finset.univ := by decide +kernel

def src1962 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,16,26,38,8,18,28,38]
def dst1962 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,16,26,38,6,18,28,38,8]
def cycle1962_0 : CycleData E W := ⟨3,![0,1,12,13,10],![2,6,5,28,14]⟩
def cycle1962_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle1962_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1962_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1962_4 : CycleData E W := ⟨3,![16,8,21,22,19],![6,16,18,28,38]⟩
def cycle1962_5 : CycleData E W := ⟨1,![9,17,14],![14,16,26]⟩
def data1962 : PartitionData E W := ⟨6,![cycle1962_0,cycle1962_1,cycle1962_2,cycle1962_3,cycle1962_4,cycle1962_5]⟩
lemma valid_data1962 : data1962.Valid src1962 dst1962 Finset.univ := by decide +kernel

def src1963 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,16,26,38,8,18,38,28]
def dst1963 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,16,26,38,6,18,38,28,8]
def cycle1963_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1963_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1963_2 : CycleData E W := ⟨2,![5,23,13,10],![2,8,28,14]⟩
def cycle1963_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1963_4 : CycleData E W := ⟨1,![9,17,14],![14,16,26]⟩
def cycle1963_5 : CycleData E W := ⟨3,![11,12,22,18,15],![4,5,28,38,26]⟩
def data1963 : PartitionData E W := ⟨6,![cycle1963_0,cycle1963_1,cycle1963_2,cycle1963_3,cycle1963_4,cycle1963_5]⟩
lemma valid_data1963 : data1963.Valid src1963 dst1963 Finset.univ := by decide +kernel

def src1964 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,16,26,38,8,28,18,38]
def dst1964 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,16,26,38,6,28,18,38,8]
def cycle1964_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1964_1 : CycleData E W := ⟨3,![3,11,12,21,7],![3,4,5,28,18]⟩
def cycle1964_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1964_3 : CycleData E W := ⟨2,![5,20,13,10],![2,8,28,14]⟩
def cycle1964_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1964_5 : CycleData E W := ⟨1,![9,17,14],![14,16,26]⟩
def data1964 : PartitionData E W := ⟨6,![cycle1964_0,cycle1964_1,cycle1964_2,cycle1964_3,cycle1964_4,cycle1964_5]⟩
lemma valid_data1964 : data1964.Valid src1964 dst1964 Finset.univ := by decide +kernel

def src1965 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,16,38,26,8,18,28,38]
def dst1965 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,16,38,26,6,18,28,38,8]
def cycle1965_0 : CycleData E W := ⟨3,![0,1,12,13,10],![2,6,5,28,14]⟩
def cycle1965_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle1965_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1965_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1965_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle1965_5 : CycleData E W := ⟨2,![16,9,14,19],![6,16,14,26]⟩
def data1965 : PartitionData E W := ⟨6,![cycle1965_0,cycle1965_1,cycle1965_2,cycle1965_3,cycle1965_4,cycle1965_5]⟩
lemma valid_data1965 : data1965.Valid src1965 dst1965 Finset.univ := by decide +kernel

def src1966 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,16,38,26,8,18,38,28]
def dst1966 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,16,38,26,6,18,38,28,8]
def cycle1966_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1966_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1966_2 : CycleData E W := ⟨2,![5,23,13,10],![2,8,28,14]⟩
def cycle1966_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1966_4 : CycleData E W := ⟨2,![16,9,14,19],![6,16,14,26]⟩
def cycle1966_5 : CycleData E W := ⟨3,![11,12,22,18,15],![4,5,28,38,26]⟩
def data1966 : PartitionData E W := ⟨6,![cycle1966_0,cycle1966_1,cycle1966_2,cycle1966_3,cycle1966_4,cycle1966_5]⟩
lemma valid_data1966 : data1966.Valid src1966 dst1966 Finset.univ := by decide +kernel

def src1967 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,16,38,26,8,28,18,38]
def dst1967 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,16,38,26,6,28,18,38,8]
def cycle1967_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1967_1 : CycleData E W := ⟨3,![3,11,12,21,7],![3,4,5,28,18]⟩
def cycle1967_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1967_3 : CycleData E W := ⟨2,![5,20,13,10],![2,8,28,14]⟩
def cycle1967_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1967_5 : CycleData E W := ⟨2,![16,9,14,19],![6,16,14,26]⟩
def data1967 : PartitionData E W := ⟨6,![cycle1967_0,cycle1967_1,cycle1967_2,cycle1967_3,cycle1967_4,cycle1967_5]⟩
lemma valid_data1967 : data1967.Valid src1967 dst1967 Finset.univ := by decide +kernel

def src1968 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,26,16,38,8,18,28,38]
def dst1968 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,26,16,38,6,18,28,38,8]
def cycle1968_0 : CycleData E W := ⟨3,![0,1,12,13,10],![2,6,5,28,14]⟩
def cycle1968_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle1968_2 : CycleData E W := ⟨3,![4,23,19,16,15],![4,8,38,6,26]⟩
def cycle1968_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1968_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle1968_5 : CycleData E W := ⟨1,![9,17,14],![14,16,26]⟩
def data1968 : PartitionData E W := ⟨6,![cycle1968_0,cycle1968_1,cycle1968_2,cycle1968_3,cycle1968_4,cycle1968_5]⟩
lemma valid_data1968 : data1968.Valid src1968 dst1968 Finset.univ := by decide +kernel

def src1969 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,26,16,38,8,18,38,28]
def dst1969 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,26,16,38,6,18,38,28,8]
def cycle1969_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1969_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1969_2 : CycleData E W := ⟨2,![5,23,13,10],![2,8,28,14]⟩
def cycle1969_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1969_4 : CycleData E W := ⟨1,![9,17,14],![14,16,26]⟩
def cycle1969_5 : CycleData E W := ⟨4,![11,12,22,19,16,15],![4,5,28,38,6,26]⟩
def data1969 : PartitionData E W := ⟨6,![cycle1969_0,cycle1969_1,cycle1969_2,cycle1969_3,cycle1969_4,cycle1969_5]⟩
lemma valid_data1969 : data1969.Valid src1969 dst1969 Finset.univ := by decide +kernel

def src1970 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,5,28,14,26,6,26,16,38,8,28,18,38]
def dst1970 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,5,28,14,26,4,26,16,38,6,28,18,38,8]
def cycle1970_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1970_1 : CycleData E W := ⟨3,![3,11,12,21,7],![3,4,5,28,18]⟩
def cycle1970_2 : CycleData E W := ⟨3,![4,23,19,16,15],![4,8,38,6,26]⟩
def cycle1970_3 : CycleData E W := ⟨2,![5,20,13,10],![2,8,28,14]⟩
def cycle1970_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1970_5 : CycleData E W := ⟨1,![9,17,14],![14,16,26]⟩
def data1970 : PartitionData E W := ⟨6,![cycle1970_0,cycle1970_1,cycle1970_2,cycle1970_3,cycle1970_4,cycle1970_5]⟩
lemma valid_data1970 : data1970.Valid src1970 dst1970 Finset.univ := by decide +kernel

def src1971 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,16,26,38,8,18,28,38]
def dst1971 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,16,26,38,6,18,28,38,8]
def cycle1971_0 : CycleData E W := ⟨2,![0,1,12,10],![2,6,5,14]⟩
def cycle1971_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle1971_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,4,3]⟩
def cycle1971_3 : CycleData E W := ⟨3,![16,8,20,23,19],![6,16,18,8,38]⟩
def cycle1971_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1971_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1971 : PartitionData E W := ⟨6,![cycle1971_0,cycle1971_1,cycle1971_2,cycle1971_3,cycle1971_4,cycle1971_5]⟩
lemma valid_data1971 : data1971.Valid src1971 dst1971 Finset.univ := by decide +kernel

def src1972 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,16,26,38,8,18,38,28]
def dst1972 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,16,26,38,6,18,38,28,8]
def cycle1972_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1972_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1972_2 : CycleData E W := ⟨3,![5,23,13,12,10],![2,8,28,5,14]⟩
def cycle1972_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1972_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1972_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1972 : PartitionData E W := ⟨6,![cycle1972_0,cycle1972_1,cycle1972_2,cycle1972_3,cycle1972_4,cycle1972_5]⟩
lemma valid_data1972 : data1972.Valid src1972 dst1972 Finset.univ := by decide +kernel

def src1973 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,16,26,38,8,28,18,38]
def dst1973 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,16,26,38,6,28,18,38,8]
def cycle1973_0 : CycleData E W := ⟨2,![0,1,12,10],![2,6,5,14]⟩
def cycle1973_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle1973_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,4,3]⟩
def cycle1973_3 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1973_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1973_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1973 : PartitionData E W := ⟨6,![cycle1973_0,cycle1973_1,cycle1973_2,cycle1973_3,cycle1973_4,cycle1973_5]⟩
lemma valid_data1973 : data1973.Valid src1973 dst1973 Finset.univ := by decide +kernel

def src1974 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,16,38,26,8,18,28,38]
def dst1974 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,16,38,26,6,18,28,38,8]
def cycle1974_0 : CycleData E W := ⟨2,![0,1,12,10],![2,6,5,14]⟩
def cycle1974_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle1974_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,4,3]⟩
def cycle1974_3 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle1974_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle1974_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1974 : PartitionData E W := ⟨6,![cycle1974_0,cycle1974_1,cycle1974_2,cycle1974_3,cycle1974_4,cycle1974_5]⟩
lemma valid_data1974 : data1974.Valid src1974 dst1974 Finset.univ := by decide +kernel

def src1975 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,16,38,26,8,18,38,28]
def dst1975 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,16,38,26,6,18,38,28,8]
def cycle1975_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1975_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1975_2 : CycleData E W := ⟨3,![5,23,13,12,10],![2,8,28,5,14]⟩
def cycle1975_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1975_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle1975_5 : CycleData E W := ⟨1,![14,22,18],![26,28,38]⟩
def data1975 : PartitionData E W := ⟨6,![cycle1975_0,cycle1975_1,cycle1975_2,cycle1975_3,cycle1975_4,cycle1975_5]⟩
lemma valid_data1975 : data1975.Valid src1975 dst1975 Finset.univ := by decide +kernel

def src1976 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,16,38,26,8,28,18,38]
def dst1976 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,16,38,26,6,28,18,38,8]
def cycle1976_0 : CycleData E W := ⟨2,![0,1,12,10],![2,6,5,14]⟩
def cycle1976_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle1976_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,4,3]⟩
def cycle1976_3 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1976_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle1976_5 : CycleData E W := ⟨2,![20,14,18,23],![8,28,26,38]⟩
def data1976 : PartitionData E W := ⟨6,![cycle1976_0,cycle1976_1,cycle1976_2,cycle1976_3,cycle1976_4,cycle1976_5]⟩
lemma valid_data1976 : data1976.Valid src1976 dst1976 Finset.univ := by decide +kernel

def src1977 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,26,16,38,8,18,28,38]
def dst1977 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,26,16,38,6,18,28,38,8]
def cycle1977_0 : CycleData E W := ⟨2,![0,1,12,10],![2,6,5,14]⟩
def cycle1977_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle1977_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,4,3]⟩
def cycle1977_3 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1977_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1977_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1977 : PartitionData E W := ⟨6,![cycle1977_0,cycle1977_1,cycle1977_2,cycle1977_3,cycle1977_4,cycle1977_5]⟩
lemma valid_data1977 : data1977.Valid src1977 dst1977 Finset.univ := by decide +kernel

def src1978 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,26,16,38,8,18,38,28]
def dst1978 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,26,16,38,6,18,38,28,8]
def cycle1978_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1978_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1978_2 : CycleData E W := ⟨3,![5,23,13,12,10],![2,8,28,5,14]⟩
def cycle1978_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1978_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1978_5 : CycleData E W := ⟨2,![16,14,22,19],![6,26,28,38]⟩
def data1978 : PartitionData E W := ⟨6,![cycle1978_0,cycle1978_1,cycle1978_2,cycle1978_3,cycle1978_4,cycle1978_5]⟩
lemma valid_data1978 : data1978.Valid src1978 dst1978 Finset.univ := by decide +kernel

def src1979 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,5,28,26,6,26,16,38,8,28,18,38]
def dst1979 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,5,28,26,4,26,16,38,6,28,18,38,8]
def cycle1979_0 : CycleData E W := ⟨2,![0,1,12,10],![2,6,5,14]⟩
def cycle1979_1 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle1979_2 : CycleData E W := ⟨2,![5,4,3,6],![2,8,4,3]⟩
def cycle1979_3 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1979_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1979_5 : CycleData E W := ⟨3,![16,14,20,23,19],![6,26,28,8,38]⟩
def data1979 : PartitionData E W := ⟨6,![cycle1979_0,cycle1979_1,cycle1979_2,cycle1979_3,cycle1979_4,cycle1979_5]⟩
lemma valid_data1979 : data1979.Valid src1979 dst1979 Finset.univ := by decide +kernel

def src1980 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,16,26,38,8,18,28,38]
def dst1980 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,16,26,38,6,18,28,38,8]
def cycle1980_0 : CycleData E W := ⟨10,![0,19,18,14,13,12,9,8,20,4,3,6],![2,6,38,26,5,28,14,16,18,8,4,3]⟩
def cycle1980_1 : CycleData E W := ⟨10,![5,23,22,21,7,2,1,16,17,15,11,10],![2,8,38,28,18,3,5,6,16,26,4,14]⟩
def data1980 : PartitionData E W := ⟨2,![cycle1980_0,cycle1980_1]⟩
lemma valid_data1980 : data1980.Valid src1980 dst1980 Finset.univ := by decide +kernel

def src1981 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,16,26,38,8,18,38,28]
def dst1981 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,16,26,38,6,18,38,28,8]
def cycle1981_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1981_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1981_2 : CycleData E W := ⟨2,![5,23,12,10],![2,8,28,14]⟩
def cycle1981_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1981_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1981_5 : CycleData E W := ⟨2,![13,22,18,14],![5,28,38,26]⟩
def data1981 : PartitionData E W := ⟨6,![cycle1981_0,cycle1981_1,cycle1981_2,cycle1981_3,cycle1981_4,cycle1981_5]⟩
lemma valid_data1981 : data1981.Valid src1981 dst1981 Finset.univ := by decide +kernel

def src1982 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,16,26,38,8,28,18,38]
def dst1982 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,16,26,38,6,28,18,38,8]
def cycle1982_0 : CycleData E W := ⟨10,![0,19,18,14,13,20,4,3,7,8,9,10],![2,6,38,26,5,28,8,4,3,18,16,14]⟩
def cycle1982_1 : CycleData E W := ⟨10,![5,23,22,21,12,11,15,17,16,1,2,6],![2,8,38,18,28,14,4,26,16,6,5,3]⟩
def data1982 : PartitionData E W := ⟨2,![cycle1982_0,cycle1982_1]⟩
lemma valid_data1982 : data1982.Valid src1982 dst1982 Finset.univ := by decide +kernel

def src1983 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,16,38,26,8,18,28,38]
def dst1983 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,16,38,26,6,18,28,38,8]
def cycle1983_0 : CycleData E W := ⟨2,![0,16,9,10],![2,6,16,14]⟩
def cycle1983_1 : CycleData E W := ⟨1,![1,19,14],![5,6,26]⟩
def cycle1983_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle1983_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1983_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1983_5 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def data1983 : PartitionData E W := ⟨6,![cycle1983_0,cycle1983_1,cycle1983_2,cycle1983_3,cycle1983_4,cycle1983_5]⟩
lemma valid_data1983 : data1983.Valid src1983 dst1983 Finset.univ := by decide +kernel

def src1984 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,16,38,26,8,18,38,28]
def dst1984 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,16,38,26,6,18,38,28,8]
def cycle1984_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1984_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1984_2 : CycleData E W := ⟨2,![5,23,12,10],![2,8,28,14]⟩
def cycle1984_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1984_4 : CycleData E W := ⟨3,![11,9,16,19,15],![4,14,16,6,26]⟩
def cycle1984_5 : CycleData E W := ⟨2,![13,22,18,14],![5,28,38,26]⟩
def data1984 : PartitionData E W := ⟨6,![cycle1984_0,cycle1984_1,cycle1984_2,cycle1984_3,cycle1984_4,cycle1984_5]⟩
lemma valid_data1984 : data1984.Valid src1984 dst1984 Finset.univ := by decide +kernel

def src1985 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,16,38,26,8,28,18,38]
def dst1985 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,16,38,26,6,28,18,38,8]
def cycle1985_0 : CycleData E W := ⟨2,![0,16,9,10],![2,6,16,14]⟩
def cycle1985_1 : CycleData E W := ⟨1,![1,19,14],![5,6,26]⟩
def cycle1985_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle1985_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1985_4 : CycleData E W := ⟨3,![5,20,21,7,6],![2,8,28,18,3]⟩
def cycle1985_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data1985 : PartitionData E W := ⟨6,![cycle1985_0,cycle1985_1,cycle1985_2,cycle1985_3,cycle1985_4,cycle1985_5]⟩
lemma valid_data1985 : data1985.Valid src1985 dst1985 Finset.univ := by decide +kernel

def src1986 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,26,16,38,8,18,28,38]
def dst1986 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,26,16,38,6,18,28,38,8]
def cycle1986_0 : CycleData E W := ⟨3,![0,19,22,12,10],![2,6,38,28,14]⟩
def cycle1986_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle1986_2 : CycleData E W := ⟨2,![2,13,21,7],![3,5,28,18]⟩
def cycle1986_3 : CycleData E W := ⟨2,![5,4,3,6],![2,8,4,3]⟩
def cycle1986_4 : CycleData E W := ⟨2,![20,8,18,23],![8,18,16,38]⟩
def cycle1986_5 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def data1986 : PartitionData E W := ⟨6,![cycle1986_0,cycle1986_1,cycle1986_2,cycle1986_3,cycle1986_4,cycle1986_5]⟩
lemma valid_data1986 : data1986.Valid src1986 dst1986 Finset.univ := by decide +kernel

def src1987 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,26,16,38,8,18,38,28]
def dst1987 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,26,16,38,6,18,38,28,8]
def cycle1987_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1987_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1987_2 : CycleData E W := ⟨2,![5,23,12,10],![2,8,28,14]⟩
def cycle1987_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1987_4 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def cycle1987_5 : CycleData E W := ⟨3,![13,22,19,16,14],![5,28,38,6,26]⟩
def data1987 : PartitionData E W := ⟨6,![cycle1987_0,cycle1987_1,cycle1987_2,cycle1987_3,cycle1987_4,cycle1987_5]⟩
lemma valid_data1987 : data1987.Valid src1987 dst1987 Finset.univ := by decide +kernel

def src1988 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,14,28,5,26,6,26,16,38,8,28,18,38]
def dst1988 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,14,28,5,26,4,26,16,38,6,28,18,38,8]
def cycle1988_0 : CycleData E W := ⟨2,![0,19,23,5],![2,6,38,8]⟩
def cycle1988_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle1988_2 : CycleData E W := ⟨3,![6,2,13,12,10],![2,3,5,28,14]⟩
def cycle1988_3 : CycleData E W := ⟨3,![3,4,20,21,7],![3,4,8,28,18]⟩
def cycle1988_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1988_5 : CycleData E W := ⟨2,![11,9,17,15],![4,14,16,26]⟩
def data1988 : PartitionData E W := ⟨6,![cycle1988_0,cycle1988_1,cycle1988_2,cycle1988_3,cycle1988_4,cycle1988_5]⟩
lemma valid_data1988 : data1988.Valid src1988 dst1988 Finset.univ := by decide +kernel

def src1989 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,16,26,38,8,18,28,38]
def dst1989 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,16,26,38,6,18,28,38,8]
def cycle1989_0 : CycleData E W := ⟨2,![0,1,13,10],![2,6,5,14]⟩
def cycle1989_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle1989_2 : CycleData E W := ⟨2,![4,23,18,11],![4,8,38,26]⟩
def cycle1989_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1989_4 : CycleData E W := ⟨3,![16,8,21,22,19],![6,16,18,28,38]⟩
def cycle1989_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1989 : PartitionData E W := ⟨6,![cycle1989_0,cycle1989_1,cycle1989_2,cycle1989_3,cycle1989_4,cycle1989_5]⟩
lemma valid_data1989 : data1989.Valid src1989 dst1989 Finset.univ := by decide +kernel

def src1990 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,16,26,38,8,18,38,28]
def dst1990 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,16,26,38,6,18,38,28,8]
def cycle1990_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1990_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1990_2 : CycleData E W := ⟨3,![5,23,14,13,10],![2,8,28,5,14]⟩
def cycle1990_3 : CycleData E W := ⟨2,![16,8,21,19],![6,16,18,38]⟩
def cycle1990_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle1990_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1990 : PartitionData E W := ⟨6,![cycle1990_0,cycle1990_1,cycle1990_2,cycle1990_3,cycle1990_4,cycle1990_5]⟩
lemma valid_data1990 : data1990.Valid src1990 dst1990 Finset.univ := by decide +kernel

def src1991 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,16,26,38,8,28,18,38]
def dst1991 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,16,26,38,6,28,18,38,8]
def cycle1991_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1991_1 : CycleData E W := ⟨2,![3,15,21,7],![3,4,28,18]⟩
def cycle1991_2 : CycleData E W := ⟨2,![4,23,18,11],![4,8,38,26]⟩
def cycle1991_3 : CycleData E W := ⟨3,![5,20,14,13,10],![2,8,28,5,14]⟩
def cycle1991_4 : CycleData E W := ⟨2,![16,8,22,19],![6,16,18,38]⟩
def cycle1991_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1991 : PartitionData E W := ⟨6,![cycle1991_0,cycle1991_1,cycle1991_2,cycle1991_3,cycle1991_4,cycle1991_5]⟩
lemma valid_data1991 : data1991.Valid src1991 dst1991 Finset.univ := by decide +kernel

def src1992 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,16,38,26,8,18,28,38]
def dst1992 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,16,38,26,6,18,28,38,8]
def cycle1992_0 : CycleData E W := ⟨2,![0,1,13,10],![2,6,5,14]⟩
def cycle1992_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle1992_2 : CycleData E W := ⟨2,![4,23,18,11],![4,8,38,26]⟩
def cycle1992_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1992_4 : CycleData E W := ⟨2,![8,21,22,17],![16,18,28,38]⟩
def cycle1992_5 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def data1992 : PartitionData E W := ⟨6,![cycle1992_0,cycle1992_1,cycle1992_2,cycle1992_3,cycle1992_4,cycle1992_5]⟩
lemma valid_data1992 : data1992.Valid src1992 dst1992 Finset.univ := by decide +kernel

def src1993 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,16,38,26,8,18,38,28]
def dst1993 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,16,38,26,6,18,38,28,8]
def cycle1993_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1993_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1993_2 : CycleData E W := ⟨3,![5,23,14,13,10],![2,8,28,5,14]⟩
def cycle1993_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle1993_4 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def cycle1993_5 : CycleData E W := ⟨2,![11,18,22,15],![4,26,38,28]⟩
def data1993 : PartitionData E W := ⟨6,![cycle1993_0,cycle1993_1,cycle1993_2,cycle1993_3,cycle1993_4,cycle1993_5]⟩
lemma valid_data1993 : data1993.Valid src1993 dst1993 Finset.univ := by decide +kernel

def src1994 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,16,38,26,8,28,18,38]
def dst1994 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,16,38,26,6,28,18,38,8]
def cycle1994_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1994_1 : CycleData E W := ⟨2,![3,15,21,7],![3,4,28,18]⟩
def cycle1994_2 : CycleData E W := ⟨2,![4,23,18,11],![4,8,38,26]⟩
def cycle1994_3 : CycleData E W := ⟨3,![5,20,14,13,10],![2,8,28,5,14]⟩
def cycle1994_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle1994_5 : CycleData E W := ⟨2,![16,9,12,19],![6,16,14,26]⟩
def data1994 : PartitionData E W := ⟨6,![cycle1994_0,cycle1994_1,cycle1994_2,cycle1994_3,cycle1994_4,cycle1994_5]⟩
lemma valid_data1994 : data1994.Valid src1994 dst1994 Finset.univ := by decide +kernel

def src1995 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,26,16,38,8,18,28,38]
def dst1995 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,26,16,38,6,18,28,38,8]
def cycle1995_0 : CycleData E W := ⟨2,![0,1,13,10],![2,6,5,14]⟩
def cycle1995_1 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle1995_2 : CycleData E W := ⟨3,![4,23,19,16,11],![4,8,38,6,26]⟩
def cycle1995_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,3]⟩
def cycle1995_4 : CycleData E W := ⟨2,![8,21,22,18],![16,18,28,38]⟩
def cycle1995_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1995 : PartitionData E W := ⟨6,![cycle1995_0,cycle1995_1,cycle1995_2,cycle1995_3,cycle1995_4,cycle1995_5]⟩
lemma valid_data1995 : data1995.Valid src1995 dst1995 Finset.univ := by decide +kernel

def src1996 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,26,16,38,8,18,38,28]
def dst1996 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,26,16,38,6,18,38,28,8]
def cycle1996_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1996_1 : CycleData E W := ⟨2,![3,4,20,7],![3,4,8,18]⟩
def cycle1996_2 : CycleData E W := ⟨3,![5,23,14,13,10],![2,8,28,5,14]⟩
def cycle1996_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle1996_4 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def cycle1996_5 : CycleData E W := ⟨3,![11,16,19,22,15],![4,26,6,38,28]⟩
def data1996 : PartitionData E W := ⟨6,![cycle1996_0,cycle1996_1,cycle1996_2,cycle1996_3,cycle1996_4,cycle1996_5]⟩
lemma valid_data1996 : data1996.Valid src1996 dst1996 Finset.univ := by decide +kernel

def src1997 : E → W := ![2,6,5,3,4,8,2,3,18,16,14,4,26,14,5,28,6,26,16,38,8,28,18,38]
def dst1997 : E → W := ![6,5,3,4,8,2,3,18,16,14,2,26,14,5,28,4,26,16,38,6,28,18,38,8]
def cycle1997_0 : CycleData E W := ⟨2,![0,1,2,6],![2,6,5,3]⟩
def cycle1997_1 : CycleData E W := ⟨2,![3,15,21,7],![3,4,28,18]⟩
def cycle1997_2 : CycleData E W := ⟨3,![4,23,19,16,11],![4,8,38,6,26]⟩
def cycle1997_3 : CycleData E W := ⟨3,![5,20,14,13,10],![2,8,28,5,14]⟩
def cycle1997_4 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def cycle1997_5 : CycleData E W := ⟨1,![9,17,12],![14,16,26]⟩
def data1997 : PartitionData E W := ⟨6,![cycle1997_0,cycle1997_1,cycle1997_2,cycle1997_3,cycle1997_4,cycle1997_5]⟩
lemma valid_data1997 : data1997.Valid src1997 dst1997 Finset.univ := by decide +kernel

def src1998 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,16,26,38,8,18,28,38]
def dst1998 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,16,26,38,6,18,28,38,8]
def cycle1998_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle1998_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle1998_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle1998_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1998_4 : CycleData E W := ⟨2,![7,14,17,8],![3,14,26,16]⟩
def cycle1998_5 : CycleData E W := ⟨3,![16,9,21,22,19],![6,16,18,28,38]⟩
def data1998 : PartitionData E W := ⟨6,![cycle1998_0,cycle1998_1,cycle1998_2,cycle1998_3,cycle1998_4,cycle1998_5]⟩
lemma valid_data1998 : data1998.Valid src1998 dst1998 Finset.univ := by decide +kernel

def src1999 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,16,26,38,8,18,38,28]
def dst1999 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,16,26,38,6,18,38,28,8]
def cycle1999_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,6,5,3,14]⟩
def cycle1999_1 : CycleData E W := ⟨2,![3,15,17,8],![3,4,26,16]⟩
def cycle1999_2 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,5]⟩
def cycle1999_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle1999_4 : CycleData E W := ⟨2,![16,9,21,19],![6,16,18,38]⟩
def cycle1999_5 : CycleData E W := ⟨2,![13,22,18,14],![14,28,38,26]⟩
def data1999 : PartitionData E W := ⟨6,![cycle1999_0,cycle1999_1,cycle1999_2,cycle1999_3,cycle1999_4,cycle1999_5]⟩
lemma valid_data1999 : data1999.Valid src1999 dst1999 Finset.univ := by decide +kernel

def lookupB9 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data1800 else (if j < 2 then data1801 else data1802)) else (if j < 4 then data1803 else (if j < 5 then data1804 else data1805))) else (if j < 9 then (if j < 7 then data1806 else (if j < 8 then data1807 else data1808)) else (if j < 10 then data1809 else (if j < 11 then data1810 else data1811)))) else (if j < 18 then (if j < 15 then (if j < 13 then data1812 else (if j < 14 then data1813 else data1814)) else (if j < 16 then data1815 else (if j < 17 then data1816 else data1817))) else (if j < 21 then (if j < 19 then data1818 else (if j < 20 then data1819 else data1820)) else (if j < 23 then (if j < 22 then data1821 else data1822) else (if j < 24 then data1823 else data1824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data1825 else (if j < 27 then data1826 else data1827)) else (if j < 29 then data1828 else (if j < 30 then data1829 else data1830))) else (if j < 34 then (if j < 32 then data1831 else (if j < 33 then data1832 else data1833)) else (if j < 35 then data1834 else (if j < 36 then data1835 else data1836)))) else (if j < 43 then (if j < 40 then (if j < 38 then data1837 else (if j < 39 then data1838 else data1839)) else (if j < 41 then data1840 else (if j < 42 then data1841 else data1842))) else (if j < 46 then (if j < 44 then data1843 else (if j < 45 then data1844 else data1845)) else (if j < 48 then (if j < 47 then data1846 else data1847) else (if j < 49 then data1848 else data1849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data1850 else (if j < 52 then data1851 else data1852)) else (if j < 54 then data1853 else (if j < 55 then data1854 else data1855))) else (if j < 59 then (if j < 57 then data1856 else (if j < 58 then data1857 else data1858)) else (if j < 60 then data1859 else (if j < 61 then data1860 else data1861)))) else (if j < 68 then (if j < 65 then (if j < 63 then data1862 else (if j < 64 then data1863 else data1864)) else (if j < 66 then data1865 else (if j < 67 then data1866 else data1867))) else (if j < 71 then (if j < 69 then data1868 else (if j < 70 then data1869 else data1870)) else (if j < 73 then (if j < 72 then data1871 else data1872) else (if j < 74 then data1873 else data1874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data1875 else (if j < 77 then data1876 else data1877)) else (if j < 79 then data1878 else (if j < 80 then data1879 else data1880))) else (if j < 84 then (if j < 82 then data1881 else (if j < 83 then data1882 else data1883)) else (if j < 85 then data1884 else (if j < 86 then data1885 else data1886)))) else (if j < 93 then (if j < 90 then (if j < 88 then data1887 else (if j < 89 then data1888 else data1889)) else (if j < 91 then data1890 else (if j < 92 then data1891 else data1892))) else (if j < 96 then (if j < 94 then data1893 else (if j < 95 then data1894 else data1895)) else (if j < 98 then (if j < 97 then data1896 else data1897) else (if j < 99 then data1898 else data1899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data1900 else (if j < 102 then data1901 else data1902)) else (if j < 104 then data1903 else (if j < 105 then data1904 else data1905))) else (if j < 109 then (if j < 107 then data1906 else (if j < 108 then data1907 else data1908)) else (if j < 110 then data1909 else (if j < 111 then data1910 else data1911)))) else (if j < 118 then (if j < 115 then (if j < 113 then data1912 else (if j < 114 then data1913 else data1914)) else (if j < 116 then data1915 else (if j < 117 then data1916 else data1917))) else (if j < 121 then (if j < 119 then data1918 else (if j < 120 then data1919 else data1920)) else (if j < 123 then (if j < 122 then data1921 else data1922) else (if j < 124 then data1923 else data1924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data1925 else (if j < 127 then data1926 else data1927)) else (if j < 129 then data1928 else (if j < 130 then data1929 else data1930))) else (if j < 134 then (if j < 132 then data1931 else (if j < 133 then data1932 else data1933)) else (if j < 135 then data1934 else (if j < 136 then data1935 else data1936)))) else (if j < 143 then (if j < 140 then (if j < 138 then data1937 else (if j < 139 then data1938 else data1939)) else (if j < 141 then data1940 else (if j < 142 then data1941 else data1942))) else (if j < 146 then (if j < 144 then data1943 else (if j < 145 then data1944 else data1945)) else (if j < 148 then (if j < 147 then data1946 else data1947) else (if j < 149 then data1948 else data1949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data1950 else (if j < 152 then data1951 else data1952)) else (if j < 154 then data1953 else (if j < 155 then data1954 else data1955))) else (if j < 159 then (if j < 157 then data1956 else (if j < 158 then data1957 else data1958)) else (if j < 160 then data1959 else (if j < 161 then data1960 else data1961)))) else (if j < 168 then (if j < 165 then (if j < 163 then data1962 else (if j < 164 then data1963 else data1964)) else (if j < 166 then data1965 else (if j < 167 then data1966 else data1967))) else (if j < 171 then (if j < 169 then data1968 else (if j < 170 then data1969 else data1970)) else (if j < 173 then (if j < 172 then data1971 else data1972) else (if j < 174 then data1973 else data1974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data1975 else (if j < 177 then data1976 else data1977)) else (if j < 179 then data1978 else (if j < 180 then data1979 else data1980))) else (if j < 184 then (if j < 182 then data1981 else (if j < 183 then data1982 else data1983)) else (if j < 185 then data1984 else (if j < 186 then data1985 else data1986)))) else (if j < 193 then (if j < 190 then (if j < 188 then data1987 else (if j < 189 then data1988 else data1989)) else (if j < 191 then data1990 else (if j < 192 then data1991 else data1992))) else (if j < 196 then (if j < 194 then data1993 else (if j < 195 then data1994 else data1995)) else (if j < 198 then (if j < 197 then data1996 else data1997) else (if j < 199 then data1998 else data1999))))))))

def srcTableB9 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src1800 else (if j < 2 then src1801 else src1802)) else (if j < 4 then src1803 else (if j < 5 then src1804 else src1805))) else (if j < 9 then (if j < 7 then src1806 else (if j < 8 then src1807 else src1808)) else (if j < 10 then src1809 else (if j < 11 then src1810 else src1811)))) else (if j < 18 then (if j < 15 then (if j < 13 then src1812 else (if j < 14 then src1813 else src1814)) else (if j < 16 then src1815 else (if j < 17 then src1816 else src1817))) else (if j < 21 then (if j < 19 then src1818 else (if j < 20 then src1819 else src1820)) else (if j < 23 then (if j < 22 then src1821 else src1822) else (if j < 24 then src1823 else src1824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src1825 else (if j < 27 then src1826 else src1827)) else (if j < 29 then src1828 else (if j < 30 then src1829 else src1830))) else (if j < 34 then (if j < 32 then src1831 else (if j < 33 then src1832 else src1833)) else (if j < 35 then src1834 else (if j < 36 then src1835 else src1836)))) else (if j < 43 then (if j < 40 then (if j < 38 then src1837 else (if j < 39 then src1838 else src1839)) else (if j < 41 then src1840 else (if j < 42 then src1841 else src1842))) else (if j < 46 then (if j < 44 then src1843 else (if j < 45 then src1844 else src1845)) else (if j < 48 then (if j < 47 then src1846 else src1847) else (if j < 49 then src1848 else src1849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src1850 else (if j < 52 then src1851 else src1852)) else (if j < 54 then src1853 else (if j < 55 then src1854 else src1855))) else (if j < 59 then (if j < 57 then src1856 else (if j < 58 then src1857 else src1858)) else (if j < 60 then src1859 else (if j < 61 then src1860 else src1861)))) else (if j < 68 then (if j < 65 then (if j < 63 then src1862 else (if j < 64 then src1863 else src1864)) else (if j < 66 then src1865 else (if j < 67 then src1866 else src1867))) else (if j < 71 then (if j < 69 then src1868 else (if j < 70 then src1869 else src1870)) else (if j < 73 then (if j < 72 then src1871 else src1872) else (if j < 74 then src1873 else src1874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src1875 else (if j < 77 then src1876 else src1877)) else (if j < 79 then src1878 else (if j < 80 then src1879 else src1880))) else (if j < 84 then (if j < 82 then src1881 else (if j < 83 then src1882 else src1883)) else (if j < 85 then src1884 else (if j < 86 then src1885 else src1886)))) else (if j < 93 then (if j < 90 then (if j < 88 then src1887 else (if j < 89 then src1888 else src1889)) else (if j < 91 then src1890 else (if j < 92 then src1891 else src1892))) else (if j < 96 then (if j < 94 then src1893 else (if j < 95 then src1894 else src1895)) else (if j < 98 then (if j < 97 then src1896 else src1897) else (if j < 99 then src1898 else src1899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src1900 else (if j < 102 then src1901 else src1902)) else (if j < 104 then src1903 else (if j < 105 then src1904 else src1905))) else (if j < 109 then (if j < 107 then src1906 else (if j < 108 then src1907 else src1908)) else (if j < 110 then src1909 else (if j < 111 then src1910 else src1911)))) else (if j < 118 then (if j < 115 then (if j < 113 then src1912 else (if j < 114 then src1913 else src1914)) else (if j < 116 then src1915 else (if j < 117 then src1916 else src1917))) else (if j < 121 then (if j < 119 then src1918 else (if j < 120 then src1919 else src1920)) else (if j < 123 then (if j < 122 then src1921 else src1922) else (if j < 124 then src1923 else src1924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src1925 else (if j < 127 then src1926 else src1927)) else (if j < 129 then src1928 else (if j < 130 then src1929 else src1930))) else (if j < 134 then (if j < 132 then src1931 else (if j < 133 then src1932 else src1933)) else (if j < 135 then src1934 else (if j < 136 then src1935 else src1936)))) else (if j < 143 then (if j < 140 then (if j < 138 then src1937 else (if j < 139 then src1938 else src1939)) else (if j < 141 then src1940 else (if j < 142 then src1941 else src1942))) else (if j < 146 then (if j < 144 then src1943 else (if j < 145 then src1944 else src1945)) else (if j < 148 then (if j < 147 then src1946 else src1947) else (if j < 149 then src1948 else src1949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src1950 else (if j < 152 then src1951 else src1952)) else (if j < 154 then src1953 else (if j < 155 then src1954 else src1955))) else (if j < 159 then (if j < 157 then src1956 else (if j < 158 then src1957 else src1958)) else (if j < 160 then src1959 else (if j < 161 then src1960 else src1961)))) else (if j < 168 then (if j < 165 then (if j < 163 then src1962 else (if j < 164 then src1963 else src1964)) else (if j < 166 then src1965 else (if j < 167 then src1966 else src1967))) else (if j < 171 then (if j < 169 then src1968 else (if j < 170 then src1969 else src1970)) else (if j < 173 then (if j < 172 then src1971 else src1972) else (if j < 174 then src1973 else src1974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src1975 else (if j < 177 then src1976 else src1977)) else (if j < 179 then src1978 else (if j < 180 then src1979 else src1980))) else (if j < 184 then (if j < 182 then src1981 else (if j < 183 then src1982 else src1983)) else (if j < 185 then src1984 else (if j < 186 then src1985 else src1986)))) else (if j < 193 then (if j < 190 then (if j < 188 then src1987 else (if j < 189 then src1988 else src1989)) else (if j < 191 then src1990 else (if j < 192 then src1991 else src1992))) else (if j < 196 then (if j < 194 then src1993 else (if j < 195 then src1994 else src1995)) else (if j < 198 then (if j < 197 then src1996 else src1997) else (if j < 199 then src1998 else src1999))))))))

def dstTableB9 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst1800 else (if j < 2 then dst1801 else dst1802)) else (if j < 4 then dst1803 else (if j < 5 then dst1804 else dst1805))) else (if j < 9 then (if j < 7 then dst1806 else (if j < 8 then dst1807 else dst1808)) else (if j < 10 then dst1809 else (if j < 11 then dst1810 else dst1811)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst1812 else (if j < 14 then dst1813 else dst1814)) else (if j < 16 then dst1815 else (if j < 17 then dst1816 else dst1817))) else (if j < 21 then (if j < 19 then dst1818 else (if j < 20 then dst1819 else dst1820)) else (if j < 23 then (if j < 22 then dst1821 else dst1822) else (if j < 24 then dst1823 else dst1824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst1825 else (if j < 27 then dst1826 else dst1827)) else (if j < 29 then dst1828 else (if j < 30 then dst1829 else dst1830))) else (if j < 34 then (if j < 32 then dst1831 else (if j < 33 then dst1832 else dst1833)) else (if j < 35 then dst1834 else (if j < 36 then dst1835 else dst1836)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst1837 else (if j < 39 then dst1838 else dst1839)) else (if j < 41 then dst1840 else (if j < 42 then dst1841 else dst1842))) else (if j < 46 then (if j < 44 then dst1843 else (if j < 45 then dst1844 else dst1845)) else (if j < 48 then (if j < 47 then dst1846 else dst1847) else (if j < 49 then dst1848 else dst1849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst1850 else (if j < 52 then dst1851 else dst1852)) else (if j < 54 then dst1853 else (if j < 55 then dst1854 else dst1855))) else (if j < 59 then (if j < 57 then dst1856 else (if j < 58 then dst1857 else dst1858)) else (if j < 60 then dst1859 else (if j < 61 then dst1860 else dst1861)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst1862 else (if j < 64 then dst1863 else dst1864)) else (if j < 66 then dst1865 else (if j < 67 then dst1866 else dst1867))) else (if j < 71 then (if j < 69 then dst1868 else (if j < 70 then dst1869 else dst1870)) else (if j < 73 then (if j < 72 then dst1871 else dst1872) else (if j < 74 then dst1873 else dst1874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst1875 else (if j < 77 then dst1876 else dst1877)) else (if j < 79 then dst1878 else (if j < 80 then dst1879 else dst1880))) else (if j < 84 then (if j < 82 then dst1881 else (if j < 83 then dst1882 else dst1883)) else (if j < 85 then dst1884 else (if j < 86 then dst1885 else dst1886)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst1887 else (if j < 89 then dst1888 else dst1889)) else (if j < 91 then dst1890 else (if j < 92 then dst1891 else dst1892))) else (if j < 96 then (if j < 94 then dst1893 else (if j < 95 then dst1894 else dst1895)) else (if j < 98 then (if j < 97 then dst1896 else dst1897) else (if j < 99 then dst1898 else dst1899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst1900 else (if j < 102 then dst1901 else dst1902)) else (if j < 104 then dst1903 else (if j < 105 then dst1904 else dst1905))) else (if j < 109 then (if j < 107 then dst1906 else (if j < 108 then dst1907 else dst1908)) else (if j < 110 then dst1909 else (if j < 111 then dst1910 else dst1911)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst1912 else (if j < 114 then dst1913 else dst1914)) else (if j < 116 then dst1915 else (if j < 117 then dst1916 else dst1917))) else (if j < 121 then (if j < 119 then dst1918 else (if j < 120 then dst1919 else dst1920)) else (if j < 123 then (if j < 122 then dst1921 else dst1922) else (if j < 124 then dst1923 else dst1924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst1925 else (if j < 127 then dst1926 else dst1927)) else (if j < 129 then dst1928 else (if j < 130 then dst1929 else dst1930))) else (if j < 134 then (if j < 132 then dst1931 else (if j < 133 then dst1932 else dst1933)) else (if j < 135 then dst1934 else (if j < 136 then dst1935 else dst1936)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst1937 else (if j < 139 then dst1938 else dst1939)) else (if j < 141 then dst1940 else (if j < 142 then dst1941 else dst1942))) else (if j < 146 then (if j < 144 then dst1943 else (if j < 145 then dst1944 else dst1945)) else (if j < 148 then (if j < 147 then dst1946 else dst1947) else (if j < 149 then dst1948 else dst1949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst1950 else (if j < 152 then dst1951 else dst1952)) else (if j < 154 then dst1953 else (if j < 155 then dst1954 else dst1955))) else (if j < 159 then (if j < 157 then dst1956 else (if j < 158 then dst1957 else dst1958)) else (if j < 160 then dst1959 else (if j < 161 then dst1960 else dst1961)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst1962 else (if j < 164 then dst1963 else dst1964)) else (if j < 166 then dst1965 else (if j < 167 then dst1966 else dst1967))) else (if j < 171 then (if j < 169 then dst1968 else (if j < 170 then dst1969 else dst1970)) else (if j < 173 then (if j < 172 then dst1971 else dst1972) else (if j < 174 then dst1973 else dst1974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst1975 else (if j < 177 then dst1976 else dst1977)) else (if j < 179 then dst1978 else (if j < 180 then dst1979 else dst1980))) else (if j < 184 then (if j < 182 then dst1981 else (if j < 183 then dst1982 else dst1983)) else (if j < 185 then dst1984 else (if j < 186 then dst1985 else dst1986)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst1987 else (if j < 189 then dst1988 else dst1989)) else (if j < 191 then dst1990 else (if j < 192 then dst1991 else dst1992))) else (if j < 196 then (if j < 194 then dst1993 else (if j < 195 then dst1994 else dst1995)) else (if j < 198 then (if j < 197 then dst1996 else dst1997) else (if j < 199 then dst1998 else dst1999))))))))

def caseB9 (i : Fin 200) : Cases := ⟨1800 + i.val,by have := i.isLt; omega⟩
lemma tableB9_valid (i : Fin 200) :
    (lookupB9 i.val).Valid (srcTableB9 i.val) (dstTableB9 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data1800
  · exact valid_data1801
  · exact valid_data1802
  · exact valid_data1803
  · exact valid_data1804
  · exact valid_data1805
  · exact valid_data1806
  · exact valid_data1807
  · exact valid_data1808
  · exact valid_data1809
  · exact valid_data1810
  · exact valid_data1811
  · exact valid_data1812
  · exact valid_data1813
  · exact valid_data1814
  · exact valid_data1815
  · exact valid_data1816
  · exact valid_data1817
  · exact valid_data1818
  · exact valid_data1819
  · exact valid_data1820
  · exact valid_data1821
  · exact valid_data1822
  · exact valid_data1823
  · exact valid_data1824
  · exact valid_data1825
  · exact valid_data1826
  · exact valid_data1827
  · exact valid_data1828
  · exact valid_data1829
  · exact valid_data1830
  · exact valid_data1831
  · exact valid_data1832
  · exact valid_data1833
  · exact valid_data1834
  · exact valid_data1835
  · exact valid_data1836
  · exact valid_data1837
  · exact valid_data1838
  · exact valid_data1839
  · exact valid_data1840
  · exact valid_data1841
  · exact valid_data1842
  · exact valid_data1843
  · exact valid_data1844
  · exact valid_data1845
  · exact valid_data1846
  · exact valid_data1847
  · exact valid_data1848
  · exact valid_data1849
  · exact valid_data1850
  · exact valid_data1851
  · exact valid_data1852
  · exact valid_data1853
  · exact valid_data1854
  · exact valid_data1855
  · exact valid_data1856
  · exact valid_data1857
  · exact valid_data1858
  · exact valid_data1859
  · exact valid_data1860
  · exact valid_data1861
  · exact valid_data1862
  · exact valid_data1863
  · exact valid_data1864
  · exact valid_data1865
  · exact valid_data1866
  · exact valid_data1867
  · exact valid_data1868
  · exact valid_data1869
  · exact valid_data1870
  · exact valid_data1871
  · exact valid_data1872
  · exact valid_data1873
  · exact valid_data1874
  · exact valid_data1875
  · exact valid_data1876
  · exact valid_data1877
  · exact valid_data1878
  · exact valid_data1879
  · exact valid_data1880
  · exact valid_data1881
  · exact valid_data1882
  · exact valid_data1883
  · exact valid_data1884
  · exact valid_data1885
  · exact valid_data1886
  · exact valid_data1887
  · exact valid_data1888
  · exact valid_data1889
  · exact valid_data1890
  · exact valid_data1891
  · exact valid_data1892
  · exact valid_data1893
  · exact valid_data1894
  · exact valid_data1895
  · exact valid_data1896
  · exact valid_data1897
  · exact valid_data1898
  · exact valid_data1899
  · exact valid_data1900
  · exact valid_data1901
  · exact valid_data1902
  · exact valid_data1903
  · exact valid_data1904
  · exact valid_data1905
  · exact valid_data1906
  · exact valid_data1907
  · exact valid_data1908
  · exact valid_data1909
  · exact valid_data1910
  · exact valid_data1911
  · exact valid_data1912
  · exact valid_data1913
  · exact valid_data1914
  · exact valid_data1915
  · exact valid_data1916
  · exact valid_data1917
  · exact valid_data1918
  · exact valid_data1919
  · exact valid_data1920
  · exact valid_data1921
  · exact valid_data1922
  · exact valid_data1923
  · exact valid_data1924
  · exact valid_data1925
  · exact valid_data1926
  · exact valid_data1927
  · exact valid_data1928
  · exact valid_data1929
  · exact valid_data1930
  · exact valid_data1931
  · exact valid_data1932
  · exact valid_data1933
  · exact valid_data1934
  · exact valid_data1935
  · exact valid_data1936
  · exact valid_data1937
  · exact valid_data1938
  · exact valid_data1939
  · exact valid_data1940
  · exact valid_data1941
  · exact valid_data1942
  · exact valid_data1943
  · exact valid_data1944
  · exact valid_data1945
  · exact valid_data1946
  · exact valid_data1947
  · exact valid_data1948
  · exact valid_data1949
  · exact valid_data1950
  · exact valid_data1951
  · exact valid_data1952
  · exact valid_data1953
  · exact valid_data1954
  · exact valid_data1955
  · exact valid_data1956
  · exact valid_data1957
  · exact valid_data1958
  · exact valid_data1959
  · exact valid_data1960
  · exact valid_data1961
  · exact valid_data1962
  · exact valid_data1963
  · exact valid_data1964
  · exact valid_data1965
  · exact valid_data1966
  · exact valid_data1967
  · exact valid_data1968
  · exact valid_data1969
  · exact valid_data1970
  · exact valid_data1971
  · exact valid_data1972
  · exact valid_data1973
  · exact valid_data1974
  · exact valid_data1975
  · exact valid_data1976
  · exact valid_data1977
  · exact valid_data1978
  · exact valid_data1979
  · exact valid_data1980
  · exact valid_data1981
  · exact valid_data1982
  · exact valid_data1983
  · exact valid_data1984
  · exact valid_data1985
  · exact valid_data1986
  · exact valid_data1987
  · exact valid_data1988
  · exact valid_data1989
  · exact valid_data1990
  · exact valid_data1991
  · exact valid_data1992
  · exact valid_data1993
  · exact valid_data1994
  · exact valid_data1995
  · exact valid_data1996
  · exact valid_data1997
  · exact valid_data1998
  · exact valid_data1999

lemma srcB9_row : ∀ (i : Fin 200) (e : E),
    srcTableB9 i.val e = caseSource (caseB9 i) e := by decide +kernel

lemma dstB9_row : ∀ (i : Fin 200) (e : E),
    dstTableB9 i.val e = caseTarget (caseB9 i) e := by decide +kernel

lemma sizeB9 : ∀ i : Fin 200, (lookupB9 i.val).size ≤ 5 →
    (lookupB9 i.val).size = 2 ∧
      (⟨caseKey (caseB9 i),caseKey_lt (caseB9 i)⟩ : Fin 77760) ∈ good := by decide +kernel
lemma certificateB9 (i : Fin 200) : Certificate (caseB9 i) := by
  refine ⟨lookupB9 i.val,?_,sizeB9 i⟩
  have hv := tableB9_valid i
  rw [funext (srcB9_row i),funext (dstB9_row i)] at hv
  exact hv
lemma certificateInterval9 : FiniteIntervals.Covers CertificateAt 1800 2000 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 1800 200 (fun i _ => certificateB9 i)
#print axioms certificateInterval9
end Erdos184Work.FiveRows2

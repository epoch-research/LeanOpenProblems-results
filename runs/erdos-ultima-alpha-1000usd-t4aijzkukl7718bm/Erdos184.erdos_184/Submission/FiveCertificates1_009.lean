import Submission.FiveCertificates1Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows1
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src1800 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1800 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1800_0 : CycleData E W := ⟨9,![0,17,16,10,13,12,8,7,18,3,5],![2,6,38,26,4,28,14,16,18,8,3]⟩
def cycle1800_1 : CycleData E W := ⟨9,![4,21,20,19,6,2,1,14,15,11,9],![2,8,38,28,18,3,4,6,16,26,14]⟩
def data1800 : PartitionData E W := ⟨2,![cycle1800_0,cycle1800_1]⟩
lemma valid_data1800 : data1800.Valid src1800 dst1800 Finset.univ := by decide +kernel

def src1801 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1801 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1801_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1801_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1801_2 : CycleData E W := ⟨2,![4,21,12,9],![2,8,28,14]⟩
def cycle1801_3 : CycleData E W := ⟨2,![14,7,19,17],![6,16,18,38]⟩
def cycle1801_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1801_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1801 : PartitionData E W := ⟨6,![cycle1801_0,cycle1801_1,cycle1801_2,cycle1801_3,cycle1801_4,cycle1801_5]⟩
lemma valid_data1801 : data1801.Valid src1801 dst1801 Finset.univ := by decide +kernel

def src1802 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1802 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1802_0 : CycleData E W := ⟨9,![0,17,16,10,2,6,7,8,12,18,4],![2,6,38,26,4,3,18,16,14,28,8]⟩
def cycle1802_1 : CycleData E W := ⟨9,![5,3,21,20,19,13,1,14,15,11,9],![2,3,8,38,18,28,4,6,16,26,14]⟩
def data1802 : PartitionData E W := ⟨2,![cycle1802_0,cycle1802_1]⟩
lemma valid_data1802 : data1802.Valid src1802 dst1802 Finset.univ := by decide +kernel

def src1803 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1803 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1803_0 : CycleData E W := ⟨2,![0,14,8,9],![2,6,16,14]⟩
def cycle1803_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1803_2 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1803_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1803_4 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle1803_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1803 : PartitionData E W := ⟨6,![cycle1803_0,cycle1803_1,cycle1803_2,cycle1803_3,cycle1803_4,cycle1803_5]⟩
lemma valid_data1803 : data1803.Valid src1803 dst1803 Finset.univ := by decide +kernel

def src1804 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1804 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1804_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1804_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1804_2 : CycleData E W := ⟨2,![4,21,12,9],![2,8,28,14]⟩
def cycle1804_3 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle1804_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle1804_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1804 : PartitionData E W := ⟨6,![cycle1804_0,cycle1804_1,cycle1804_2,cycle1804_3,cycle1804_4,cycle1804_5]⟩
lemma valid_data1804 : data1804.Valid src1804 dst1804 Finset.univ := by decide +kernel

def src1805 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1805 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1805_0 : CycleData E W := ⟨2,![0,14,8,9],![2,6,16,14]⟩
def cycle1805_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1805_2 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1805_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1805_4 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle1805_5 : CycleData E W := ⟨3,![18,12,11,16,21],![8,28,14,26,38]⟩
def data1805 : PartitionData E W := ⟨6,![cycle1805_0,cycle1805_1,cycle1805_2,cycle1805_3,cycle1805_4,cycle1805_5]⟩
lemma valid_data1805 : data1805.Valid src1805 dst1805 Finset.univ := by decide +kernel

def src1806 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1806 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1806_0 : CycleData E W := ⟨3,![0,17,20,12,9],![2,6,38,28,14]⟩
def cycle1806_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1806_2 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1806_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1806_4 : CycleData E W := ⟨2,![18,7,16,21],![8,18,16,38]⟩
def cycle1806_5 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data1806 : PartitionData E W := ⟨6,![cycle1806_0,cycle1806_1,cycle1806_2,cycle1806_3,cycle1806_4,cycle1806_5]⟩
lemma valid_data1806 : data1806.Valid src1806 dst1806 Finset.univ := by decide +kernel

def src1807 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1807 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1807_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1807_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1807_2 : CycleData E W := ⟨2,![4,21,12,9],![2,8,28,14]⟩
def cycle1807_3 : CycleData E W := ⟨1,![7,19,16],![16,18,38]⟩
def cycle1807_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1807_5 : CycleData E W := ⟨3,![10,14,17,20,13],![4,26,6,38,28]⟩
def data1807 : PartitionData E W := ⟨6,![cycle1807_0,cycle1807_1,cycle1807_2,cycle1807_3,cycle1807_4,cycle1807_5]⟩
lemma valid_data1807 : data1807.Valid src1807 dst1807 Finset.univ := by decide +kernel

def src1808 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1808 : E → W := ![6,4,3,8,2,3,18,16,14,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1808_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1808_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1808_2 : CycleData E W := ⟨3,![5,2,13,12,9],![2,3,4,28,14]⟩
def cycle1808_3 : CycleData E W := ⟨2,![3,18,19,6],![3,8,28,18]⟩
def cycle1808_4 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle1808_5 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def data1808 : PartitionData E W := ⟨6,![cycle1808_0,cycle1808_1,cycle1808_2,cycle1808_3,cycle1808_4,cycle1808_5]⟩
lemma valid_data1808 : data1808.Valid src1808 dst1808 Finset.univ := by decide +kernel

def src1809 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1809 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1809_0 : CycleData E W := ⟨9,![0,17,16,12,13,10,6,7,8,18,4],![2,6,38,26,28,4,14,3,16,18,8]⟩
def cycle1809_1 : CycleData E W := ⟨9,![5,11,15,14,1,2,3,21,20,19,9],![2,14,26,16,6,4,3,8,38,28,18]⟩
def data1809 : PartitionData E W := ⟨2,![cycle1809_0,cycle1809_1]⟩
lemma valid_data1809 : data1809.Valid src1809 dst1809 Finset.univ := by decide +kernel

def src1810 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1810 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1810_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1810_1 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1810_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1810_3 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1810_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1810_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1810 : PartitionData E W := ⟨6,![cycle1810_0,cycle1810_1,cycle1810_2,cycle1810_3,cycle1810_4,cycle1810_5]⟩
lemma valid_data1810 : data1810.Valid src1810 dst1810 Finset.univ := by decide +kernel

def src1811 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1811 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1811_0 : CycleData E W := ⟨9,![5,10,1,17,16,12,18,3,7,8,9],![2,14,4,6,38,26,28,8,3,16,18]⟩
def cycle1811_1 : CycleData E W := ⟨9,![0,14,15,11,6,2,13,19,20,21,4],![2,6,16,26,14,3,4,28,18,38,8]⟩
def data1811 : PartitionData E W := ⟨2,![cycle1811_0,cycle1811_1]⟩
lemma valid_data1811 : data1811.Valid src1811 dst1811 Finset.univ := by decide +kernel

def src1812 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1812 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1812_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1812_1 : CycleData E W := ⟨3,![1,14,8,19,13],![4,6,16,18,28]⟩
def cycle1812_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1812_3 : CycleData E W := ⟨2,![3,21,15,7],![3,8,38,16]⟩
def cycle1812_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1812_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1812 : PartitionData E W := ⟨6,![cycle1812_0,cycle1812_1,cycle1812_2,cycle1812_3,cycle1812_4,cycle1812_5]⟩
lemma valid_data1812 : data1812.Valid src1812 dst1812 Finset.univ := by decide +kernel

def src1813 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1813 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1813_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1813_1 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1813_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1813_3 : CycleData E W := ⟨3,![6,11,17,14,7],![3,14,26,6,16]⟩
def cycle1813_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1813_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1813 : PartitionData E W := ⟨6,![cycle1813_0,cycle1813_1,cycle1813_2,cycle1813_3,cycle1813_4,cycle1813_5]⟩
lemma valid_data1813 : data1813.Valid src1813 dst1813 Finset.univ := by decide +kernel

def src1814 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1814 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1814_0 : CycleData E W := ⟨9,![0,1,10,6,3,18,12,16,15,8,9],![2,6,4,14,3,8,28,26,38,16,18]⟩
def cycle1814_1 : CycleData E W := ⟨9,![4,21,20,19,13,2,7,14,17,11,5],![2,8,38,18,28,4,3,16,6,26,14]⟩
def data1814 : PartitionData E W := ⟨2,![cycle1814_0,cycle1814_1]⟩
lemma valid_data1814 : data1814.Valid src1814 dst1814 Finset.univ := by decide +kernel

def src1815 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1815 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1815_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1815_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1815_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1815_3 : CycleData E W := ⟨2,![3,21,16,7],![3,8,38,16]⟩
def cycle1815_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1815_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1815 : PartitionData E W := ⟨6,![cycle1815_0,cycle1815_1,cycle1815_2,cycle1815_3,cycle1815_4,cycle1815_5]⟩
lemma valid_data1815 : data1815.Valid src1815 dst1815 Finset.univ := by decide +kernel

def src1816 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1816 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1816_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1816_1 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1816_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1816_3 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1816_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1816_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1816 : PartitionData E W := ⟨6,![cycle1816_0,cycle1816_1,cycle1816_2,cycle1816_3,cycle1816_4,cycle1816_5]⟩
lemma valid_data1816 : data1816.Valid src1816 dst1816 Finset.univ := by decide +kernel

def src1817 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1817 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1817_0 : CycleData E W := ⟨9,![5,11,12,18,3,2,1,17,16,8,9],![2,14,26,28,8,3,4,6,38,16,18]⟩
def cycle1817_1 : CycleData E W := ⟨9,![0,14,15,7,6,10,13,19,20,21,4],![2,6,26,16,3,14,4,28,18,38,8]⟩
def data1817 : PartitionData E W := ⟨2,![cycle1817_0,cycle1817_1]⟩
lemma valid_data1817 : data1817.Valid src1817 dst1817 Finset.univ := by decide +kernel

def src1818 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1818 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1818_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1818_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1818_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1818_3 : CycleData E W := ⟨2,![3,18,8,7],![3,8,18,16]⟩
def cycle1818_4 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle1818_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1818 : PartitionData E W := ⟨6,![cycle1818_0,cycle1818_1,cycle1818_2,cycle1818_3,cycle1818_4,cycle1818_5]⟩
lemma valid_data1818 : data1818.Valid src1818 dst1818 Finset.univ := by decide +kernel

def src1819 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1819 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1819_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1819_1 : CycleData E W := ⟨2,![2,13,15,7],![3,4,26,16]⟩
def cycle1819_2 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1819_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1819_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1819_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1819 : PartitionData E W := ⟨6,![cycle1819_0,cycle1819_1,cycle1819_2,cycle1819_3,cycle1819_4,cycle1819_5]⟩
lemma valid_data1819 : data1819.Valid src1819 dst1819 Finset.univ := by decide +kernel

def src1820 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1820 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1820_0 : CycleData E W := ⟨9,![5,10,1,17,16,12,18,3,7,8,9],![2,14,4,6,38,26,28,8,3,16,18]⟩
def cycle1820_1 : CycleData E W := ⟨9,![0,14,15,13,2,6,11,19,20,21,4],![2,6,16,26,4,3,14,28,18,38,8]⟩
def data1820 : PartitionData E W := ⟨2,![cycle1820_0,cycle1820_1]⟩
lemma valid_data1820 : data1820.Valid src1820 dst1820 Finset.univ := by decide +kernel

def src1821 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1821 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1821_0 : CycleData E W := ⟨3,![0,14,7,3,4],![2,6,16,3,8]⟩
def cycle1821_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1821_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1821_3 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle1821_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1821_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1821 : PartitionData E W := ⟨6,![cycle1821_0,cycle1821_1,cycle1821_2,cycle1821_3,cycle1821_4,cycle1821_5]⟩
lemma valid_data1821 : data1821.Valid src1821 dst1821 Finset.univ := by decide +kernel

def src1822 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1822 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1822_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1822_1 : CycleData E W := ⟨3,![2,13,17,14,7],![3,4,26,6,16]⟩
def cycle1822_2 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1822_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1822_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1822_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1822 : PartitionData E W := ⟨6,![cycle1822_0,cycle1822_1,cycle1822_2,cycle1822_3,cycle1822_4,cycle1822_5]⟩
lemma valid_data1822 : data1822.Valid src1822 dst1822 Finset.univ := by decide +kernel

def src1823 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1823 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1823_0 : CycleData E W := ⟨3,![0,14,7,3,4],![2,6,16,3,8]⟩
def cycle1823_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1823_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1823_3 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle1823_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1823_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1823 : PartitionData E W := ⟨6,![cycle1823_0,cycle1823_1,cycle1823_2,cycle1823_3,cycle1823_4,cycle1823_5]⟩
lemma valid_data1823 : data1823.Valid src1823 dst1823 Finset.univ := by decide +kernel

def src1824 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1824 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1824_0 : CycleData E W := ⟨3,![0,17,20,11,5],![2,6,38,28,14]⟩
def cycle1824_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1824_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1824_3 : CycleData E W := ⟨2,![3,21,16,7],![3,8,38,16]⟩
def cycle1824_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1824_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1824 : PartitionData E W := ⟨6,![cycle1824_0,cycle1824_1,cycle1824_2,cycle1824_3,cycle1824_4,cycle1824_5]⟩
lemma valid_data1824 : data1824.Valid src1824 dst1824 Finset.univ := by decide +kernel

def src1825 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1825 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1825_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1825_1 : CycleData E W := ⟨2,![2,13,15,7],![3,4,26,16]⟩
def cycle1825_2 : CycleData E W := ⟨2,![3,21,11,6],![3,8,28,14]⟩
def cycle1825_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1825_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1825_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1825 : PartitionData E W := ⟨6,![cycle1825_0,cycle1825_1,cycle1825_2,cycle1825_3,cycle1825_4,cycle1825_5]⟩
lemma valid_data1825 : data1825.Valid src1825 dst1825 Finset.univ := by decide +kernel

def src1826 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1826 : E → W := ![6,4,3,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1826_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1826_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1826_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1826_3 : CycleData E W := ⟨2,![3,21,16,7],![3,8,38,16]⟩
def cycle1826_4 : CycleData E W := ⟨2,![4,18,11,5],![2,8,28,14]⟩
def cycle1826_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1826 : PartitionData E W := ⟨6,![cycle1826_0,cycle1826_1,cycle1826_2,cycle1826_3,cycle1826_4,cycle1826_5]⟩
lemma valid_data1826 : data1826.Valid src1826 dst1826 Finset.univ := by decide +kernel

def src1827 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1827 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1827_0 : CycleData E W := ⟨9,![0,17,16,10,13,12,6,7,8,18,4],![2,6,38,26,4,28,14,3,16,18,8]⟩
def cycle1827_1 : CycleData E W := ⟨9,![5,11,15,14,1,2,3,21,20,19,9],![2,14,26,16,6,4,3,8,38,28,18]⟩
def data1827 : PartitionData E W := ⟨2,![cycle1827_0,cycle1827_1]⟩
lemma valid_data1827 : data1827.Valid src1827 dst1827 Finset.univ := by decide +kernel

def src1828 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1828 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1828_0 : CycleData E W := ⟨9,![0,17,16,10,13,12,6,7,8,18,4],![2,6,38,26,4,28,14,3,16,18,8]⟩
def cycle1828_1 : CycleData E W := ⟨9,![5,11,15,14,1,2,3,21,20,19,9],![2,14,26,16,6,4,3,8,28,38,18]⟩
def data1828 : PartitionData E W := ⟨2,![cycle1828_0,cycle1828_1]⟩
lemma valid_data1828 : data1828.Valid src1828 dst1828 Finset.univ := by decide +kernel

def src1829 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1829 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1829_0 : CycleData E W := ⟨9,![4,18,12,11,16,17,1,2,7,8,9],![2,8,28,14,26,38,6,4,3,16,18]⟩
def cycle1829_1 : CycleData E W := ⟨9,![0,14,15,10,13,19,20,21,3,6,5],![2,6,16,26,4,28,18,38,8,3,14]⟩
def data1829 : PartitionData E W := ⟨2,![cycle1829_0,cycle1829_1]⟩
lemma valid_data1829 : data1829.Valid src1829 dst1829 Finset.univ := by decide +kernel

def src1830 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1830 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1830_0 : CycleData E W := ⟨9,![0,1,13,12,11,16,15,7,3,18,9],![2,6,4,28,14,26,38,16,3,8,18]⟩
def cycle1830_1 : CycleData E W := ⟨9,![4,21,20,19,8,14,17,10,2,6,5],![2,8,38,28,18,16,6,26,4,3,14]⟩
def data1830 : PartitionData E W := ⟨2,![cycle1830_0,cycle1830_1]⟩
lemma valid_data1830 : data1830.Valid src1830 dst1830 Finset.univ := by decide +kernel

def src1831 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1831 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1831_0 : CycleData E W := ⟨3,![0,14,7,6,5],![2,6,16,3,14]⟩
def cycle1831_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1831_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1831_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1831_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1831_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1831 : PartitionData E W := ⟨6,![cycle1831_0,cycle1831_1,cycle1831_2,cycle1831_3,cycle1831_4,cycle1831_5]⟩
lemma valid_data1831 : data1831.Valid src1831 dst1831 Finset.univ := by decide +kernel

def src1832 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1832 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1832_0 : CycleData E W := ⟨9,![0,1,2,3,18,12,11,16,15,8,9],![2,6,4,3,8,28,14,26,38,16,18]⟩
def cycle1832_1 : CycleData E W := ⟨9,![4,21,20,19,13,10,17,14,7,6,5],![2,8,38,18,28,4,26,6,16,3,14]⟩
def data1832 : PartitionData E W := ⟨2,![cycle1832_0,cycle1832_1]⟩
lemma valid_data1832 : data1832.Valid src1832 dst1832 Finset.univ := by decide +kernel

def src1833 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1833 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1833_0 : CycleData E W := ⟨9,![5,12,13,10,14,17,16,7,3,18,9],![2,14,28,4,26,6,38,16,3,8,18]⟩
def cycle1833_1 : CycleData E W := ⟨9,![0,1,2,6,11,15,8,19,20,21,4],![2,6,4,3,14,26,16,18,28,38,8]⟩
def data1833 : PartitionData E W := ⟨2,![cycle1833_0,cycle1833_1]⟩
lemma valid_data1833 : data1833.Valid src1833 dst1833 Finset.univ := by decide +kernel

def src1834 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1834 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1834_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1834_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1834_2 : CycleData E W := ⟨2,![2,10,15,7],![3,4,26,16]⟩
def cycle1834_3 : CycleData E W := ⟨2,![3,21,12,6],![3,8,28,14]⟩
def cycle1834_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1834_5 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def data1834 : PartitionData E W := ⟨6,![cycle1834_0,cycle1834_1,cycle1834_2,cycle1834_3,cycle1834_4,cycle1834_5]⟩
lemma valid_data1834 : data1834.Valid src1834 dst1834 Finset.univ := by decide +kernel

def src1835 : E → W := ![2,6,4,3,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1835 : E → W := ![6,4,3,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1835_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1835_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1835_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1835_3 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle1835_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1835_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1835 : PartitionData E W := ⟨6,![cycle1835_0,cycle1835_1,cycle1835_2,cycle1835_3,cycle1835_4,cycle1835_5]⟩
lemma valid_data1835 : data1835.Valid src1835 dst1835 Finset.univ := by decide +kernel

def src1836 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1836 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1836_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1836_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1836_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1836_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1836_4 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1836_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1836 : PartitionData E W := ⟨6,![cycle1836_0,cycle1836_1,cycle1836_2,cycle1836_3,cycle1836_4,cycle1836_5]⟩
lemma valid_data1836 : data1836.Valid src1836 dst1836 Finset.univ := by decide +kernel

def src1837 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1837 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1837_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1837_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1837_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1837_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1837_4 : CycleData E W := ⟨3,![4,21,12,11,5],![2,8,28,26,14]⟩
def cycle1837_5 : CycleData E W := ⟨2,![8,19,16,15],![16,18,38,26]⟩
def data1837 : PartitionData E W := ⟨6,![cycle1837_0,cycle1837_1,cycle1837_2,cycle1837_3,cycle1837_4,cycle1837_5]⟩
lemma valid_data1837 : data1837.Valid src1837 dst1837 Finset.univ := by decide +kernel

def src1838 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1838 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1838_0 : CycleData E W := ⟨9,![5,10,1,17,16,12,18,3,7,8,9],![2,14,4,6,38,26,28,8,3,18,16]⟩
def cycle1838_1 : CycleData E W := ⟨9,![0,14,15,11,6,2,13,19,20,21,4],![2,6,16,26,14,3,4,28,18,38,8]⟩
def data1838 : PartitionData E W := ⟨2,![cycle1838_0,cycle1838_1]⟩
lemma valid_data1838 : data1838.Valid src1838 dst1838 Finset.univ := by decide +kernel

def src1839 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1839 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1839_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1839_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1839_2 : CycleData E W := ⟨2,![2,13,19,7],![3,4,28,18]⟩
def cycle1839_3 : CycleData E W := ⟨2,![4,3,6,5],![2,8,3,14]⟩
def cycle1839_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1839_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1839 : PartitionData E W := ⟨6,![cycle1839_0,cycle1839_1,cycle1839_2,cycle1839_3,cycle1839_4,cycle1839_5]⟩
lemma valid_data1839 : data1839.Valid src1839 dst1839 Finset.univ := by decide +kernel

def src1840 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1840 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1840_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1840_1 : CycleData E W := ⟨3,![2,1,17,11,6],![3,4,6,26,14]⟩
def cycle1840_2 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1840_3 : CycleData E W := ⟨3,![4,21,13,10,5],![2,8,28,4,14]⟩
def cycle1840_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1840_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1840 : PartitionData E W := ⟨6,![cycle1840_0,cycle1840_1,cycle1840_2,cycle1840_3,cycle1840_4,cycle1840_5]⟩
lemma valid_data1840 : data1840.Valid src1840 dst1840 Finset.univ := by decide +kernel

def src1841 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1841 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1841_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1841_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1841_2 : CycleData E W := ⟨2,![2,13,19,7],![3,4,28,18]⟩
def cycle1841_3 : CycleData E W := ⟨2,![4,3,6,5],![2,8,3,14]⟩
def cycle1841_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1841_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1841 : PartitionData E W := ⟨6,![cycle1841_0,cycle1841_1,cycle1841_2,cycle1841_3,cycle1841_4,cycle1841_5]⟩
lemma valid_data1841 : data1841.Valid src1841 dst1841 Finset.univ := by decide +kernel

def src1842 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1842 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1842_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1842_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1842_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1842_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1842_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1842_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1842 : PartitionData E W := ⟨6,![cycle1842_0,cycle1842_1,cycle1842_2,cycle1842_3,cycle1842_4,cycle1842_5]⟩
lemma valid_data1842 : data1842.Valid src1842 dst1842 Finset.univ := by decide +kernel

def src1843 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1843 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1843_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1843_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1843_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1843_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1843_4 : CycleData E W := ⟨3,![4,21,12,15,9],![2,8,28,26,16]⟩
def cycle1843_5 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def data1843 : PartitionData E W := ⟨6,![cycle1843_0,cycle1843_1,cycle1843_2,cycle1843_3,cycle1843_4,cycle1843_5]⟩
lemma valid_data1843 : data1843.Valid src1843 dst1843 Finset.univ := by decide +kernel

def src1844 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1844 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1844_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1844_1 : CycleData E W := ⟨2,![1,14,12,13],![4,6,26,28]⟩
def cycle1844_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1844_3 : CycleData E W := ⟨2,![3,18,19,7],![3,8,28,18]⟩
def cycle1844_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1844_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1844 : PartitionData E W := ⟨6,![cycle1844_0,cycle1844_1,cycle1844_2,cycle1844_3,cycle1844_4,cycle1844_5]⟩
lemma valid_data1844 : data1844.Valid src1844 dst1844 Finset.univ := by decide +kernel

def src1845 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1845 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1845_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1845_1 : CycleData E W := ⟨2,![1,17,16,13],![4,6,38,26]⟩
def cycle1845_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1845_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1845_4 : CycleData E W := ⟨3,![4,21,20,11,5],![2,8,38,28,14]⟩
def cycle1845_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1845 : PartitionData E W := ⟨6,![cycle1845_0,cycle1845_1,cycle1845_2,cycle1845_3,cycle1845_4,cycle1845_5]⟩
lemma valid_data1845 : data1845.Valid src1845 dst1845 Finset.univ := by decide +kernel

def src1846 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1846 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1846_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1846_1 : CycleData E W := ⟨2,![1,17,16,13],![4,6,38,26]⟩
def cycle1846_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1846_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1846_4 : CycleData E W := ⟨2,![4,21,11,5],![2,8,28,14]⟩
def cycle1846_5 : CycleData E W := ⟨3,![8,19,20,12,15],![16,18,38,28,26]⟩
def data1846 : PartitionData E W := ⟨6,![cycle1846_0,cycle1846_1,cycle1846_2,cycle1846_3,cycle1846_4,cycle1846_5]⟩
lemma valid_data1846 : data1846.Valid src1846 dst1846 Finset.univ := by decide +kernel

def src1847 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1847 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1847_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1847_1 : CycleData E W := ⟨2,![1,17,16,13],![4,6,38,26]⟩
def cycle1847_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1847_3 : CycleData E W := ⟨2,![3,21,20,7],![3,8,38,18]⟩
def cycle1847_4 : CycleData E W := ⟨2,![4,18,11,5],![2,8,28,14]⟩
def cycle1847_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1847 : PartitionData E W := ⟨6,![cycle1847_0,cycle1847_1,cycle1847_2,cycle1847_3,cycle1847_4,cycle1847_5]⟩
lemma valid_data1847 : data1847.Valid src1847 dst1847 Finset.univ := by decide +kernel

def src1848 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1848 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1848_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1848_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1848_2 : CycleData E W := ⟨3,![4,3,2,10,5],![2,8,3,4,14]⟩
def cycle1848_3 : CycleData E W := ⟨2,![6,11,19,7],![3,14,28,18]⟩
def cycle1848_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1848_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1848 : PartitionData E W := ⟨6,![cycle1848_0,cycle1848_1,cycle1848_2,cycle1848_3,cycle1848_4,cycle1848_5]⟩
lemma valid_data1848 : data1848.Valid src1848 dst1848 Finset.univ := by decide +kernel

def src1849 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1849 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1849_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1849_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1849_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1849_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1849_4 : CycleData E W := ⟨2,![4,21,11,5],![2,8,28,14]⟩
def cycle1849_5 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1849_6 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1849 : PartitionData E W := ⟨7,![cycle1849_0,cycle1849_1,cycle1849_2,cycle1849_3,cycle1849_4,cycle1849_5,cycle1849_6]⟩
lemma valid_data1849 : data1849.Valid src1849 dst1849 Finset.univ := by decide +kernel

def src1850 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1850 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1850_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1850_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1850_2 : CycleData E W := ⟨3,![4,3,2,10,5],![2,8,3,4,14]⟩
def cycle1850_3 : CycleData E W := ⟨2,![6,11,19,7],![3,14,28,18]⟩
def cycle1850_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1850_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1850 : PartitionData E W := ⟨6,![cycle1850_0,cycle1850_1,cycle1850_2,cycle1850_3,cycle1850_4,cycle1850_5]⟩
lemma valid_data1850 : data1850.Valid src1850 dst1850 Finset.univ := by decide +kernel

def src1851 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1851 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1851_0 : CycleData E W := ⟨2,![0,17,16,9],![2,6,38,16]⟩
def cycle1851_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1851_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1851_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1851_4 : CycleData E W := ⟨3,![4,21,20,11,5],![2,8,38,28,14]⟩
def cycle1851_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1851 : PartitionData E W := ⟨6,![cycle1851_0,cycle1851_1,cycle1851_2,cycle1851_3,cycle1851_4,cycle1851_5]⟩
lemma valid_data1851 : data1851.Valid src1851 dst1851 Finset.univ := by decide +kernel

def src1852 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1852 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1852_0 : CycleData E W := ⟨3,![0,1,13,15,9],![2,6,4,26,16]⟩
def cycle1852_1 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1852_2 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1852_3 : CycleData E W := ⟨2,![4,21,11,5],![2,8,28,14]⟩
def cycle1852_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1852_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1852 : PartitionData E W := ⟨6,![cycle1852_0,cycle1852_1,cycle1852_2,cycle1852_3,cycle1852_4,cycle1852_5]⟩
lemma valid_data1852 : data1852.Valid src1852 dst1852 Finset.univ := by decide +kernel

def src1853 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1853 : E → W := ![6,4,3,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1853_0 : CycleData E W := ⟨2,![0,17,16,9],![2,6,38,16]⟩
def cycle1853_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1853_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1853_3 : CycleData E W := ⟨2,![3,21,20,7],![3,8,38,18]⟩
def cycle1853_4 : CycleData E W := ⟨2,![4,18,11,5],![2,8,28,14]⟩
def cycle1853_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1853 : PartitionData E W := ⟨6,![cycle1853_0,cycle1853_1,cycle1853_2,cycle1853_3,cycle1853_4,cycle1853_5]⟩
lemma valid_data1853 : data1853.Valid src1853 dst1853 Finset.univ := by decide +kernel

def src1854 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1854 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1854_0 : CycleData E W := ⟨9,![0,17,16,10,13,12,6,3,18,8,9],![2,6,38,26,4,28,14,3,8,18,16]⟩
def cycle1854_1 : CycleData E W := ⟨9,![4,21,20,19,7,2,1,14,15,11,5],![2,8,38,28,18,3,4,6,16,26,14]⟩
def data1854 : PartitionData E W := ⟨2,![cycle1854_0,cycle1854_1]⟩
lemma valid_data1854 : data1854.Valid src1854 dst1854 Finset.univ := by decide +kernel

def src1855 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1855 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1855_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1855_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1855_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle1855_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1855_4 : CycleData E W := ⟨2,![4,21,12,5],![2,8,28,14]⟩
def cycle1855_5 : CycleData E W := ⟨2,![8,19,16,15],![16,18,38,26]⟩
def data1855 : PartitionData E W := ⟨6,![cycle1855_0,cycle1855_1,cycle1855_2,cycle1855_3,cycle1855_4,cycle1855_5]⟩
lemma valid_data1855 : data1855.Valid src1855 dst1855 Finset.univ := by decide +kernel

def src1856 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1856 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1856_0 : CycleData E W := ⟨9,![4,18,12,11,16,17,1,2,7,8,9],![2,8,28,14,26,38,6,4,3,18,16]⟩
def cycle1856_1 : CycleData E W := ⟨9,![0,14,15,10,13,19,20,21,3,6,5],![2,6,16,26,4,28,18,38,8,3,14]⟩
def data1856 : PartitionData E W := ⟨2,![cycle1856_0,cycle1856_1]⟩
lemma valid_data1856 : data1856.Valid src1856 dst1856 Finset.univ := by decide +kernel

def src1857 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1857 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1857_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1857_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1857_2 : CycleData E W := ⟨2,![2,13,12,6],![3,4,28,14]⟩
def cycle1857_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1857_4 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1857_5 : CycleData E W := ⟨2,![8,19,20,15],![16,18,28,38]⟩
def data1857 : PartitionData E W := ⟨6,![cycle1857_0,cycle1857_1,cycle1857_2,cycle1857_3,cycle1857_4,cycle1857_5]⟩
lemma valid_data1857 : data1857.Valid src1857 dst1857 Finset.univ := by decide +kernel

def src1858 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1858 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1858_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1858_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1858_2 : CycleData E W := ⟨2,![2,13,12,6],![3,4,28,14]⟩
def cycle1858_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1858_4 : CycleData E W := ⟨4,![4,21,20,16,11,5],![2,8,28,38,26,14]⟩
def cycle1858_5 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def data1858 : PartitionData E W := ⟨6,![cycle1858_0,cycle1858_1,cycle1858_2,cycle1858_3,cycle1858_4,cycle1858_5]⟩
lemma valid_data1858 : data1858.Valid src1858 dst1858 Finset.univ := by decide +kernel

def src1859 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1859 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1859_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1859_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1859_2 : CycleData E W := ⟨2,![2,13,12,6],![3,4,28,14]⟩
def cycle1859_3 : CycleData E W := ⟨2,![3,18,19,7],![3,8,28,18]⟩
def cycle1859_4 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1859_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data1859 : PartitionData E W := ⟨6,![cycle1859_0,cycle1859_1,cycle1859_2,cycle1859_3,cycle1859_4,cycle1859_5]⟩
lemma valid_data1859 : data1859.Valid src1859 dst1859 Finset.univ := by decide +kernel

def src1860 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1860 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1860_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1860_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1860_2 : CycleData E W := ⟨2,![2,13,12,6],![3,4,28,14]⟩
def cycle1860_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1860_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1860_5 : CycleData E W := ⟨2,![8,19,20,16],![16,18,28,38]⟩
def data1860 : PartitionData E W := ⟨6,![cycle1860_0,cycle1860_1,cycle1860_2,cycle1860_3,cycle1860_4,cycle1860_5]⟩
lemma valid_data1860 : data1860.Valid src1860 dst1860 Finset.univ := by decide +kernel

def src1861 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1861 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1861_0 : CycleData E W := ⟨2,![0,14,15,9],![2,6,26,16]⟩
def cycle1861_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1861_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle1861_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1861_4 : CycleData E W := ⟨2,![4,21,12,5],![2,8,28,14]⟩
def cycle1861_5 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def data1861 : PartitionData E W := ⟨6,![cycle1861_0,cycle1861_1,cycle1861_2,cycle1861_3,cycle1861_4,cycle1861_5]⟩
lemma valid_data1861 : data1861.Valid src1861 dst1861 Finset.univ := by decide +kernel

def src1862 : E → W := ![2,6,4,3,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1862 : E → W := ![6,4,3,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1862_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1862_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1862_2 : CycleData E W := ⟨2,![2,13,12,6],![3,4,28,14]⟩
def cycle1862_3 : CycleData E W := ⟨2,![3,18,19,7],![3,8,28,18]⟩
def cycle1862_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1862_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1862 : PartitionData E W := ⟨6,![cycle1862_0,cycle1862_1,cycle1862_2,cycle1862_3,cycle1862_4,cycle1862_5]⟩
lemma valid_data1862 : data1862.Valid src1862 dst1862 Finset.univ := by decide +kernel

def src1863 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1863 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1863_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1863_1 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1863_2 : CycleData E W := ⟨3,![3,21,17,14,7],![3,8,38,6,16]⟩
def cycle1863_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1863_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1863_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1863 : PartitionData E W := ⟨6,![cycle1863_0,cycle1863_1,cycle1863_2,cycle1863_3,cycle1863_4,cycle1863_5]⟩
lemma valid_data1863 : data1863.Valid src1863 dst1863 Finset.univ := by decide +kernel

def src1864 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1864 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1864_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1864_1 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1864_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1864_3 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1864_4 : CycleData E W := ⟨3,![7,14,17,19,8],![3,16,6,38,18]⟩
def cycle1864_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1864 : PartitionData E W := ⟨6,![cycle1864_0,cycle1864_1,cycle1864_2,cycle1864_3,cycle1864_4,cycle1864_5]⟩
lemma valid_data1864 : data1864.Valid src1864 dst1864 Finset.univ := by decide +kernel

def src1865 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1865 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1865_0 : CycleData E W := ⟨9,![4,18,13,1,17,16,11,6,7,8,9],![2,8,28,4,6,38,26,14,16,3,18]⟩
def cycle1865_1 : CycleData E W := ⟨9,![0,14,15,12,19,20,21,3,2,10,5],![2,6,16,26,28,18,38,8,3,4,14]⟩
def data1865 : PartitionData E W := ⟨2,![cycle1865_0,cycle1865_1]⟩
lemma valid_data1865 : data1865.Valid src1865 dst1865 Finset.univ := by decide +kernel

def src1866 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1866 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1866_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1866_1 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1866_2 : CycleData E W := ⟨2,![3,21,15,7],![3,8,38,16]⟩
def cycle1866_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1866_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle1866_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1866 : PartitionData E W := ⟨6,![cycle1866_0,cycle1866_1,cycle1866_2,cycle1866_3,cycle1866_4,cycle1866_5]⟩
lemma valid_data1866 : data1866.Valid src1866 dst1866 Finset.univ := by decide +kernel

def src1867 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1867 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1867_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1867_1 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1867_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1867_3 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle1867_4 : CycleData E W := ⟨2,![7,15,19,8],![3,16,38,18]⟩
def cycle1867_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1867 : PartitionData E W := ⟨6,![cycle1867_0,cycle1867_1,cycle1867_2,cycle1867_3,cycle1867_4,cycle1867_5]⟩
lemma valid_data1867 : data1867.Valid src1867 dst1867 Finset.univ := by decide +kernel

def src1868 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1868 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1868_0 : CycleData E W := ⟨9,![0,1,10,6,15,16,12,18,3,8,9],![2,6,4,14,16,38,26,28,8,3,18]⟩
def cycle1868_1 : CycleData E W := ⟨9,![4,21,20,19,13,2,7,14,17,11,5],![2,8,38,18,28,4,3,16,6,26,14]⟩
def data1868 : PartitionData E W := ⟨2,![cycle1868_0,cycle1868_1]⟩
lemma valid_data1868 : data1868.Valid src1868 dst1868 Finset.univ := by decide +kernel

def src1869 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1869 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1869_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1869_1 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1869_2 : CycleData E W := ⟨2,![3,21,16,7],![3,8,38,16]⟩
def cycle1869_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1869_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1869_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1869 : PartitionData E W := ⟨6,![cycle1869_0,cycle1869_1,cycle1869_2,cycle1869_3,cycle1869_4,cycle1869_5]⟩
lemma valid_data1869 : data1869.Valid src1869 dst1869 Finset.univ := by decide +kernel

def src1870 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1870 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1870_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1870_1 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1870_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1870_3 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1870_4 : CycleData E W := ⟨2,![7,16,19,8],![3,16,38,18]⟩
def cycle1870_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1870 : PartitionData E W := ⟨6,![cycle1870_0,cycle1870_1,cycle1870_2,cycle1870_3,cycle1870_4,cycle1870_5]⟩
lemma valid_data1870 : data1870.Valid src1870 dst1870 Finset.univ := by decide +kernel

def src1871 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1871 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1871_0 : CycleData E W := ⟨9,![4,18,12,11,6,16,17,1,2,8,9],![2,8,28,26,14,16,38,6,4,3,18]⟩
def cycle1871_1 : CycleData E W := ⟨9,![0,14,15,7,3,21,20,19,13,10,5],![2,6,26,16,3,8,38,18,28,4,14]⟩
def data1871 : PartitionData E W := ⟨2,![cycle1871_0,cycle1871_1]⟩
lemma valid_data1871 : data1871.Valid src1871 dst1871 Finset.univ := by decide +kernel

def src1872 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1872 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1872_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1872_1 : CycleData E W := ⟨2,![2,1,14,7],![3,4,6,16]⟩
def cycle1872_2 : CycleData E W := ⟨1,![3,18,8],![3,8,18]⟩
def cycle1872_3 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle1872_4 : CycleData E W := ⟨2,![10,6,15,13],![4,14,16,26]⟩
def cycle1872_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1872 : PartitionData E W := ⟨6,![cycle1872_0,cycle1872_1,cycle1872_2,cycle1872_3,cycle1872_4,cycle1872_5]⟩
lemma valid_data1872 : data1872.Valid src1872 dst1872 Finset.univ := by decide +kernel

def src1873 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1873 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1873_0 : CycleData E W := ⟨2,![0,17,19,9],![2,6,38,18]⟩
def cycle1873_1 : CycleData E W := ⟨2,![2,1,14,7],![3,4,6,16]⟩
def cycle1873_2 : CycleData E W := ⟨1,![3,18,8],![3,8,18]⟩
def cycle1873_3 : CycleData E W := ⟨2,![4,21,11,5],![2,8,28,14]⟩
def cycle1873_4 : CycleData E W := ⟨2,![10,6,15,13],![4,14,16,26]⟩
def cycle1873_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1873 : PartitionData E W := ⟨6,![cycle1873_0,cycle1873_1,cycle1873_2,cycle1873_3,cycle1873_4,cycle1873_5]⟩
lemma valid_data1873 : data1873.Valid src1873 dst1873 Finset.univ := by decide +kernel

def src1874 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1874 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1874_0 : CycleData E W := ⟨9,![4,18,12,16,17,1,10,6,7,8,9],![2,8,28,26,38,6,4,14,16,3,18]⟩
def cycle1874_1 : CycleData E W := ⟨9,![0,14,15,13,2,3,21,20,19,11,5],![2,6,16,26,4,3,8,38,18,28,14]⟩
def data1874 : PartitionData E W := ⟨2,![cycle1874_0,cycle1874_1]⟩
lemma valid_data1874 : data1874.Valid src1874 dst1874 Finset.univ := by decide +kernel

def src1875 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1875 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1875_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1875_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1875_2 : CycleData E W := ⟨3,![2,10,11,19,8],![3,4,14,28,18]⟩
def cycle1875_3 : CycleData E W := ⟨2,![3,21,15,7],![3,8,38,16]⟩
def cycle1875_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1875_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1875 : PartitionData E W := ⟨6,![cycle1875_0,cycle1875_1,cycle1875_2,cycle1875_3,cycle1875_4,cycle1875_5]⟩
lemma valid_data1875 : data1875.Valid src1875 dst1875 Finset.univ := by decide +kernel

def src1876 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1876 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1876_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1876_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1876_2 : CycleData E W := ⟨3,![2,10,11,21,3],![3,4,14,28,8]⟩
def cycle1876_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1876_4 : CycleData E W := ⟨2,![7,15,19,8],![3,16,38,18]⟩
def cycle1876_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1876 : PartitionData E W := ⟨6,![cycle1876_0,cycle1876_1,cycle1876_2,cycle1876_3,cycle1876_4,cycle1876_5]⟩
lemma valid_data1876 : data1876.Valid src1876 dst1876 Finset.univ := by decide +kernel

def src1877 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1877 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1877_0 : CycleData E W := ⟨9,![0,1,13,16,15,6,11,18,3,8,9],![2,6,4,26,38,16,14,28,8,3,18]⟩
def cycle1877_1 : CycleData E W := ⟨9,![4,21,20,19,12,17,14,7,2,10,5],![2,8,38,18,28,26,6,16,3,4,14]⟩
def data1877 : PartitionData E W := ⟨2,![cycle1877_0,cycle1877_1]⟩
lemma valid_data1877 : data1877.Valid src1877 dst1877 Finset.univ := by decide +kernel

def src1878 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1878 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1878_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1878_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1878_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,16]⟩
def cycle1878_3 : CycleData E W := ⟨1,![3,18,8],![3,8,18]⟩
def cycle1878_4 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle1878_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1878 : PartitionData E W := ⟨6,![cycle1878_0,cycle1878_1,cycle1878_2,cycle1878_3,cycle1878_4,cycle1878_5]⟩
lemma valid_data1878 : data1878.Valid src1878 dst1878 Finset.univ := by decide +kernel

def src1879 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1879 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1879_0 : CycleData E W := ⟨2,![0,17,19,9],![2,6,38,18]⟩
def cycle1879_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1879_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,16]⟩
def cycle1879_3 : CycleData E W := ⟨1,![3,18,8],![3,8,18]⟩
def cycle1879_4 : CycleData E W := ⟨2,![4,21,11,5],![2,8,28,14]⟩
def cycle1879_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1879 : PartitionData E W := ⟨6,![cycle1879_0,cycle1879_1,cycle1879_2,cycle1879_3,cycle1879_4,cycle1879_5]⟩
lemma valid_data1879 : data1879.Valid src1879 dst1879 Finset.univ := by decide +kernel

def src1880 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1880 : E → W := ![6,4,3,8,2,14,16,3,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1880_0 : CycleData E W := ⟨9,![5,6,16,17,1,13,12,18,3,8,9],![2,14,16,38,6,4,26,28,8,3,18]⟩
def cycle1880_1 : CycleData E W := ⟨9,![0,14,15,7,2,10,11,19,20,21,4],![2,6,26,16,3,4,14,28,18,38,8]⟩
def data1880 : PartitionData E W := ⟨2,![cycle1880_0,cycle1880_1]⟩
lemma valid_data1880 : data1880.Valid src1880 dst1880 Finset.univ := by decide +kernel

def src1881 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1881 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1881_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1881_1 : CycleData E W := ⟨2,![2,1,14,7],![3,4,6,16]⟩
def cycle1881_2 : CycleData E W := ⟨1,![3,18,8],![3,8,18]⟩
def cycle1881_3 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle1881_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1881_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1881 : PartitionData E W := ⟨6,![cycle1881_0,cycle1881_1,cycle1881_2,cycle1881_3,cycle1881_4,cycle1881_5]⟩
lemma valid_data1881 : data1881.Valid src1881 dst1881 Finset.univ := by decide +kernel

def src1882 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1882 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1882_0 : CycleData E W := ⟨2,![0,17,19,9],![2,6,38,18]⟩
def cycle1882_1 : CycleData E W := ⟨2,![2,1,14,7],![3,4,6,16]⟩
def cycle1882_2 : CycleData E W := ⟨1,![3,18,8],![3,8,18]⟩
def cycle1882_3 : CycleData E W := ⟨2,![4,21,12,5],![2,8,28,14]⟩
def cycle1882_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1882_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1882 : PartitionData E W := ⟨6,![cycle1882_0,cycle1882_1,cycle1882_2,cycle1882_3,cycle1882_4,cycle1882_5]⟩
lemma valid_data1882 : data1882.Valid src1882 dst1882 Finset.univ := by decide +kernel

def src1883 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1883 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1883_0 : CycleData E W := ⟨9,![4,18,13,1,17,16,11,6,7,8,9],![2,8,28,4,6,38,26,14,16,3,18]⟩
def cycle1883_1 : CycleData E W := ⟨9,![0,14,15,10,2,3,21,20,19,12,5],![2,6,16,26,4,3,8,38,18,28,14]⟩
def data1883 : PartitionData E W := ⟨2,![cycle1883_0,cycle1883_1]⟩
lemma valid_data1883 : data1883.Valid src1883 dst1883 Finset.univ := by decide +kernel

def src1884 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1884 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1884_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1884_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1884_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1884_3 : CycleData E W := ⟨2,![3,21,15,7],![3,8,38,16]⟩
def cycle1884_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1884_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1884 : PartitionData E W := ⟨6,![cycle1884_0,cycle1884_1,cycle1884_2,cycle1884_3,cycle1884_4,cycle1884_5]⟩
lemma valid_data1884 : data1884.Valid src1884 dst1884 Finset.univ := by decide +kernel

def src1885 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1885 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1885_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1885_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1885_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1885_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1885_4 : CycleData E W := ⟨2,![7,15,19,8],![3,16,38,18]⟩
def cycle1885_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1885 : PartitionData E W := ⟨6,![cycle1885_0,cycle1885_1,cycle1885_2,cycle1885_3,cycle1885_4,cycle1885_5]⟩
lemma valid_data1885 : data1885.Valid src1885 dst1885 Finset.univ := by decide +kernel

def src1886 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1886 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1886_0 : CycleData E W := ⟨9,![0,1,10,16,15,6,12,18,3,8,9],![2,6,4,26,38,16,14,28,8,3,18]⟩
def cycle1886_1 : CycleData E W := ⟨9,![4,21,20,19,13,2,7,14,17,11,5],![2,8,38,18,28,4,3,16,6,26,14]⟩
def data1886 : PartitionData E W := ⟨2,![cycle1886_0,cycle1886_1]⟩
lemma valid_data1886 : data1886.Valid src1886 dst1886 Finset.univ := by decide +kernel

def src1887 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1887 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1887_0 : CycleData E W := ⟨3,![0,17,20,12,5],![2,6,38,28,14]⟩
def cycle1887_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1887_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1887_3 : CycleData E W := ⟨2,![3,21,16,7],![3,8,38,16]⟩
def cycle1887_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1887_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1887 : PartitionData E W := ⟨6,![cycle1887_0,cycle1887_1,cycle1887_2,cycle1887_3,cycle1887_4,cycle1887_5]⟩
lemma valid_data1887 : data1887.Valid src1887 dst1887 Finset.univ := by decide +kernel

def src1888 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1888 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1888_0 : CycleData E W := ⟨2,![0,17,19,9],![2,6,38,18]⟩
def cycle1888_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1888_2 : CycleData E W := ⟨3,![2,13,20,16,7],![3,4,28,38,16]⟩
def cycle1888_3 : CycleData E W := ⟨1,![3,18,8],![3,8,18]⟩
def cycle1888_4 : CycleData E W := ⟨2,![4,21,12,5],![2,8,28,14]⟩
def cycle1888_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1888 : PartitionData E W := ⟨6,![cycle1888_0,cycle1888_1,cycle1888_2,cycle1888_3,cycle1888_4,cycle1888_5]⟩
lemma valid_data1888 : data1888.Valid src1888 dst1888 Finset.univ := by decide +kernel

def src1889 : E → W := ![2,6,4,3,8,2,14,16,3,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1889 : E → W := ![6,4,3,8,2,14,16,3,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1889_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1889_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1889_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1889_3 : CycleData E W := ⟨2,![3,21,16,7],![3,8,38,16]⟩
def cycle1889_4 : CycleData E W := ⟨2,![4,18,12,5],![2,8,28,14]⟩
def cycle1889_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1889 : PartitionData E W := ⟨6,![cycle1889_0,cycle1889_1,cycle1889_2,cycle1889_3,cycle1889_4,cycle1889_5]⟩
lemma valid_data1889 : data1889.Valid src1889 dst1889 Finset.univ := by decide +kernel

def src1890 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1890 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1890_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1890_1 : CycleData E W := ⟨2,![2,1,14,8],![3,4,6,16]⟩
def cycle1890_2 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1890_3 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1890_4 : CycleData E W := ⟨2,![10,6,19,13],![4,14,18,28]⟩
def cycle1890_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1890 : PartitionData E W := ⟨6,![cycle1890_0,cycle1890_1,cycle1890_2,cycle1890_3,cycle1890_4,cycle1890_5]⟩
lemma valid_data1890 : data1890.Valid src1890 dst1890 Finset.univ := by decide +kernel

def src1891 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1891 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1891_0 : CycleData E W := ⟨9,![0,17,16,12,13,10,6,18,3,8,9],![2,6,38,26,28,4,14,18,8,3,16]⟩
def cycle1891_1 : CycleData E W := ⟨9,![4,21,20,19,7,2,1,14,15,11,5],![2,8,28,38,18,3,4,6,16,26,14]⟩
def data1891 : PartitionData E W := ⟨2,![cycle1891_0,cycle1891_1]⟩
lemma valid_data1891 : data1891.Valid src1891 dst1891 Finset.univ := by decide +kernel

def src1892 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1892 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1892_0 : CycleData E W := ⟨9,![4,18,13,1,17,16,11,6,7,8,9],![2,8,28,4,6,38,26,14,18,3,16]⟩
def cycle1892_1 : CycleData E W := ⟨9,![0,14,15,12,19,20,21,3,2,10,5],![2,6,16,26,28,18,38,8,3,4,14]⟩
def data1892 : PartitionData E W := ⟨2,![cycle1892_0,cycle1892_1]⟩
lemma valid_data1892 : data1892.Valid src1892 dst1892 Finset.univ := by decide +kernel

def src1893 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1893 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1893_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1893_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1893_2 : CycleData E W := ⟨2,![2,13,19,7],![3,4,28,18]⟩
def cycle1893_3 : CycleData E W := ⟨2,![3,21,15,8],![3,8,38,16]⟩
def cycle1893_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle1893_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1893 : PartitionData E W := ⟨6,![cycle1893_0,cycle1893_1,cycle1893_2,cycle1893_3,cycle1893_4,cycle1893_5]⟩
lemma valid_data1893 : data1893.Valid src1893 dst1893 Finset.univ := by decide +kernel

def src1894 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1894 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1894_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1894_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1894_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1894_3 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle1894_4 : CycleData E W := ⟨2,![7,19,15,8],![3,18,38,16]⟩
def cycle1894_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1894 : PartitionData E W := ⟨6,![cycle1894_0,cycle1894_1,cycle1894_2,cycle1894_3,cycle1894_4,cycle1894_5]⟩
lemma valid_data1894 : data1894.Valid src1894 dst1894 Finset.univ := by decide +kernel

def src1895 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1895 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1895_0 : CycleData E W := ⟨9,![0,1,10,6,7,3,18,12,16,15,9],![2,6,4,14,18,3,8,28,26,38,16]⟩
def cycle1895_1 : CycleData E W := ⟨9,![4,21,20,19,13,2,8,14,17,11,5],![2,8,38,18,28,4,3,16,6,26,14]⟩
def data1895 : PartitionData E W := ⟨2,![cycle1895_0,cycle1895_1]⟩
lemma valid_data1895 : data1895.Valid src1895 dst1895 Finset.univ := by decide +kernel

def src1896 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1896 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1896_0 : CycleData E W := ⟨9,![5,6,18,3,2,13,12,14,17,16,9],![2,14,18,8,3,4,28,26,6,38,16]⟩
def cycle1896_1 : CycleData E W := ⟨9,![0,1,10,11,15,8,7,19,20,21,4],![2,6,4,14,26,16,3,18,28,38,8]⟩
def data1896 : PartitionData E W := ⟨2,![cycle1896_0,cycle1896_1]⟩
lemma valid_data1896 : data1896.Valid src1896 dst1896 Finset.univ := by decide +kernel

def src1897 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1897 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1897_0 : CycleData E W := ⟨9,![5,6,18,3,2,13,12,14,17,16,9],![2,14,18,8,3,4,28,26,6,38,16]⟩
def cycle1897_1 : CycleData E W := ⟨9,![0,1,10,11,15,8,7,19,20,21,4],![2,6,4,14,26,16,3,18,38,28,8]⟩
def data1897 : PartitionData E W := ⟨2,![cycle1897_0,cycle1897_1]⟩
lemma valid_data1897 : data1897.Valid src1897 dst1897 Finset.univ := by decide +kernel

def src1898 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1898 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1898_0 : CycleData E W := ⟨9,![4,18,12,11,6,7,2,1,17,16,9],![2,8,28,26,14,18,3,4,6,38,16]⟩
def cycle1898_1 : CycleData E W := ⟨9,![0,14,15,8,3,21,20,19,13,10,5],![2,6,26,16,3,8,38,18,28,4,14]⟩
def data1898 : PartitionData E W := ⟨2,![cycle1898_0,cycle1898_1]⟩
lemma valid_data1898 : data1898.Valid src1898 dst1898 Finset.univ := by decide +kernel

def src1899 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1899 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1899_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1899_1 : CycleData E W := ⟨2,![2,13,15,8],![3,4,26,16]⟩
def cycle1899_2 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1899_3 : CycleData E W := ⟨3,![4,21,17,14,9],![2,8,38,6,16]⟩
def cycle1899_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1899_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1899 : PartitionData E W := ⟨6,![cycle1899_0,cycle1899_1,cycle1899_2,cycle1899_3,cycle1899_4,cycle1899_5]⟩
lemma valid_data1899 : data1899.Valid src1899 dst1899 Finset.univ := by decide +kernel

def src1900 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1900 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1900_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1900_1 : CycleData E W := ⟨3,![1,17,19,6,10],![4,6,38,18,14]⟩
def cycle1900_2 : CycleData E W := ⟨2,![2,13,15,8],![3,4,26,16]⟩
def cycle1900_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1900_4 : CycleData E W := ⟨2,![4,21,11,5],![2,8,28,14]⟩
def cycle1900_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1900 : PartitionData E W := ⟨6,![cycle1900_0,cycle1900_1,cycle1900_2,cycle1900_3,cycle1900_4,cycle1900_5]⟩
lemma valid_data1900 : data1900.Valid src1900 dst1900 Finset.univ := by decide +kernel

def src1901 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1901 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1901_0 : CycleData E W := ⟨9,![4,18,12,16,17,1,10,6,7,8,9],![2,8,28,26,38,6,4,14,18,3,16]⟩
def cycle1901_1 : CycleData E W := ⟨9,![0,14,15,13,2,3,21,20,19,11,5],![2,6,16,26,4,3,8,38,18,28,14]⟩
def data1901 : PartitionData E W := ⟨2,![cycle1901_0,cycle1901_1]⟩
lemma valid_data1901 : data1901.Valid src1901 dst1901 Finset.univ := by decide +kernel

def src1902 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1902 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1902_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1902_1 : CycleData E W := ⟨3,![2,13,17,14,8],![3,4,26,6,16]⟩
def cycle1902_2 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1902_3 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1902_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1902_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1902 : PartitionData E W := ⟨6,![cycle1902_0,cycle1902_1,cycle1902_2,cycle1902_3,cycle1902_4,cycle1902_5]⟩
lemma valid_data1902 : data1902.Valid src1902 dst1902 Finset.univ := by decide +kernel

def src1903 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1903 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1903_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1903_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1903_2 : CycleData E W := ⟨3,![4,3,2,10,5],![2,8,3,4,14]⟩
def cycle1903_3 : CycleData E W := ⟨2,![18,6,11,21],![8,18,14,28]⟩
def cycle1903_4 : CycleData E W := ⟨2,![7,19,15,8],![3,18,38,16]⟩
def cycle1903_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1903 : PartitionData E W := ⟨6,![cycle1903_0,cycle1903_1,cycle1903_2,cycle1903_3,cycle1903_4,cycle1903_5]⟩
lemma valid_data1903 : data1903.Valid src1903 dst1903 Finset.univ := by decide +kernel

def src1904 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1904 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1904_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1904_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1904_2 : CycleData E W := ⟨3,![4,3,2,10,5],![2,8,3,4,14]⟩
def cycle1904_3 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1904_4 : CycleData E W := ⟨2,![7,20,15,8],![3,18,38,16]⟩
def cycle1904_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1904 : PartitionData E W := ⟨6,![cycle1904_0,cycle1904_1,cycle1904_2,cycle1904_3,cycle1904_4,cycle1904_5]⟩
lemma valid_data1904 : data1904.Valid src1904 dst1904 Finset.univ := by decide +kernel

def src1905 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1905 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1905_0 : CycleData E W := ⟨2,![0,1,10,5],![2,6,4,14]⟩
def cycle1905_1 : CycleData E W := ⟨2,![2,13,15,8],![3,4,26,16]⟩
def cycle1905_2 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1905_3 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1905_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1905_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1905 : PartitionData E W := ⟨6,![cycle1905_0,cycle1905_1,cycle1905_2,cycle1905_3,cycle1905_4,cycle1905_5]⟩
lemma valid_data1905 : data1905.Valid src1905 dst1905 Finset.univ := by decide +kernel

def src1906 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1906 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1906_0 : CycleData E W := ⟨9,![4,18,7,2,10,11,12,14,17,16,9],![2,8,18,3,4,14,28,26,6,38,16]⟩
def cycle1906_1 : CycleData E W := ⟨9,![0,1,13,15,8,3,21,20,19,6,5],![2,6,4,26,16,3,8,28,38,18,14]⟩
def data1906 : PartitionData E W := ⟨2,![cycle1906_0,cycle1906_1]⟩
lemma valid_data1906 : data1906.Valid src1906 dst1906 Finset.univ := by decide +kernel

def src1907 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1907 : E → W := ![6,4,3,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1907_0 : CycleData E W := ⟨9,![5,6,7,3,18,12,13,1,17,16,9],![2,14,18,3,8,28,26,4,6,38,16]⟩
def cycle1907_1 : CycleData E W := ⟨9,![0,14,15,8,2,10,11,19,20,21,4],![2,6,26,16,3,4,14,28,18,38,8]⟩
def data1907 : PartitionData E W := ⟨2,![cycle1907_0,cycle1907_1]⟩
lemma valid_data1907 : data1907.Valid src1907 dst1907 Finset.univ := by decide +kernel

def src1908 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1908 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1908_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1908_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1908_2 : CycleData E W := ⟨2,![2,10,15,8],![3,4,26,16]⟩
def cycle1908_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1908_4 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1908_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data1908 : PartitionData E W := ⟨6,![cycle1908_0,cycle1908_1,cycle1908_2,cycle1908_3,cycle1908_4,cycle1908_5]⟩
lemma valid_data1908 : data1908.Valid src1908 dst1908 Finset.univ := by decide +kernel

def src1909 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1909 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1909_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1909_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1909_2 : CycleData E W := ⟨2,![2,10,15,8],![3,4,26,16]⟩
def cycle1909_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1909_4 : CycleData E W := ⟨2,![4,21,12,5],![2,8,28,14]⟩
def cycle1909_5 : CycleData E W := ⟨2,![6,19,16,11],![14,18,38,26]⟩
def data1909 : PartitionData E W := ⟨6,![cycle1909_0,cycle1909_1,cycle1909_2,cycle1909_3,cycle1909_4,cycle1909_5]⟩
lemma valid_data1909 : data1909.Valid src1909 dst1909 Finset.univ := by decide +kernel

def src1910 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1910 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1910_0 : CycleData E W := ⟨9,![4,18,13,1,17,16,11,6,7,8,9],![2,8,28,4,6,38,26,14,18,3,16]⟩
def cycle1910_1 : CycleData E W := ⟨9,![0,14,15,10,2,3,21,20,19,12,5],![2,6,16,26,4,3,8,38,18,28,14]⟩
def data1910 : PartitionData E W := ⟨2,![cycle1910_0,cycle1910_1]⟩
lemma valid_data1910 : data1910.Valid src1910 dst1910 Finset.univ := by decide +kernel

def src1911 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1911 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1911_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1911_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1911_2 : CycleData E W := ⟨2,![2,13,19,7],![3,4,28,18]⟩
def cycle1911_3 : CycleData E W := ⟨2,![3,21,15,8],![3,8,38,16]⟩
def cycle1911_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle1911_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1911 : PartitionData E W := ⟨6,![cycle1911_0,cycle1911_1,cycle1911_2,cycle1911_3,cycle1911_4,cycle1911_5]⟩
lemma valid_data1911 : data1911.Valid src1911 dst1911 Finset.univ := by decide +kernel

def src1912 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1912 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1912_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1912_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1912_2 : CycleData E W := ⟨3,![2,13,20,15,8],![3,4,28,38,16]⟩
def cycle1912_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1912_4 : CycleData E W := ⟨2,![4,21,12,5],![2,8,28,14]⟩
def cycle1912_5 : CycleData E W := ⟨2,![6,19,16,11],![14,18,38,26]⟩
def data1912 : PartitionData E W := ⟨6,![cycle1912_0,cycle1912_1,cycle1912_2,cycle1912_3,cycle1912_4,cycle1912_5]⟩
lemma valid_data1912 : data1912.Valid src1912 dst1912 Finset.univ := by decide +kernel

def src1913 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1913 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1913_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1913_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1913_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1913_3 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1913_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1913_5 : CycleData E W := ⟨2,![7,20,15,8],![3,18,38,16]⟩
def data1913 : PartitionData E W := ⟨6,![cycle1913_0,cycle1913_1,cycle1913_2,cycle1913_3,cycle1913_4,cycle1913_5]⟩
lemma valid_data1913 : data1913.Valid src1913 dst1913 Finset.univ := by decide +kernel

def src1914 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1914 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1914_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1914_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1914_2 : CycleData E W := ⟨2,![2,10,15,8],![3,4,26,16]⟩
def cycle1914_3 : CycleData E W := ⟨1,![3,18,7],![3,8,18]⟩
def cycle1914_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1914_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data1914 : PartitionData E W := ⟨6,![cycle1914_0,cycle1914_1,cycle1914_2,cycle1914_3,cycle1914_4,cycle1914_5]⟩
lemma valid_data1914 : data1914.Valid src1914 dst1914 Finset.univ := by decide +kernel

def src1915 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1915 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1915_0 : CycleData E W := ⟨9,![4,18,7,8,16,17,14,10,13,12,5],![2,8,18,3,16,38,6,26,4,28,14]⟩
def cycle1915_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,6,11,15,9],![2,6,4,3,8,28,38,18,14,26,16]⟩
def data1915 : PartitionData E W := ⟨2,![cycle1915_0,cycle1915_1]⟩
lemma valid_data1915 : data1915.Valid src1915 dst1915 Finset.univ := by decide +kernel

def src1916 : E → W := ![2,6,4,3,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1916 : E → W := ![6,4,3,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1916_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1916_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1916_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1916_3 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1916_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1916_5 : CycleData E W := ⟨2,![7,20,16,8],![3,18,38,16]⟩
def data1916 : PartitionData E W := ⟨6,![cycle1916_0,cycle1916_1,cycle1916_2,cycle1916_3,cycle1916_4,cycle1916_5]⟩
lemma valid_data1916 : data1916.Valid src1916 dst1916 Finset.univ := by decide +kernel

def src1917 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1917 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1917_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1917_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1917_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1917_3 : CycleData E W := ⟨3,![3,21,16,15,6],![3,8,38,26,16]⟩
def cycle1917_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1917_5 : CycleData E W := ⟨2,![8,19,12,11],![14,18,28,26]⟩
def data1917 : PartitionData E W := ⟨6,![cycle1917_0,cycle1917_1,cycle1917_2,cycle1917_3,cycle1917_4,cycle1917_5]⟩
lemma valid_data1917 : data1917.Valid src1917 dst1917 Finset.univ := by decide +kernel

def src1918 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1918 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1918_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1918_1 : CycleData E W := ⟨3,![1,17,19,8,10],![4,6,38,18,14]⟩
def cycle1918_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1918_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1918_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1918_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1918 : PartitionData E W := ⟨6,![cycle1918_0,cycle1918_1,cycle1918_2,cycle1918_3,cycle1918_4,cycle1918_5]⟩
lemma valid_data1918 : data1918.Valid src1918 dst1918 Finset.univ := by decide +kernel

def src1919 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1919 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1919_0 : CycleData E W := ⟨9,![5,6,3,18,12,16,17,1,10,8,9],![2,16,3,8,28,26,38,6,4,14,18]⟩
def cycle1919_1 : CycleData E W := ⟨9,![0,14,15,11,7,2,13,19,20,21,4],![2,6,16,26,14,3,4,28,18,38,8]⟩
def data1919 : PartitionData E W := ⟨2,![cycle1919_0,cycle1919_1]⟩
lemma valid_data1919 : data1919.Valid src1919 dst1919 Finset.univ := by decide +kernel

def src1920 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1920 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1920_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1920_1 : CycleData E W := ⟨3,![2,1,17,11,7],![3,4,6,26,14]⟩
def cycle1920_2 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1920_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1920_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle1920_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1920 : PartitionData E W := ⟨6,![cycle1920_0,cycle1920_1,cycle1920_2,cycle1920_3,cycle1920_4,cycle1920_5]⟩
lemma valid_data1920 : data1920.Valid src1920 dst1920 Finset.univ := by decide +kernel

def src1921 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1921 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1921_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1921_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1921_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1921_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1921_4 : CycleData E W := ⟨3,![6,15,19,8,7],![3,16,38,18,14]⟩
def cycle1921_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1921 : PartitionData E W := ⟨6,![cycle1921_0,cycle1921_1,cycle1921_2,cycle1921_3,cycle1921_4,cycle1921_5]⟩
lemma valid_data1921 : data1921.Valid src1921 dst1921 Finset.univ := by decide +kernel

def src1922 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1922 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1922_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1922_1 : CycleData E W := ⟨2,![1,17,12,13],![4,6,26,28]⟩
def cycle1922_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1922_3 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1922_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1922_5 : CycleData E W := ⟨2,![8,20,16,11],![14,18,38,26]⟩
def data1922 : PartitionData E W := ⟨6,![cycle1922_0,cycle1922_1,cycle1922_2,cycle1922_3,cycle1922_4,cycle1922_5]⟩
lemma valid_data1922 : data1922.Valid src1922 dst1922 Finset.univ := by decide +kernel

def src1923 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1923 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1923_0 : CycleData E W := ⟨2,![0,14,15,5],![2,6,26,16]⟩
def cycle1923_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1923_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1923_3 : CycleData E W := ⟨2,![3,21,16,6],![3,8,38,16]⟩
def cycle1923_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1923_5 : CycleData E W := ⟨2,![8,19,12,11],![14,18,28,26]⟩
def data1923 : PartitionData E W := ⟨6,![cycle1923_0,cycle1923_1,cycle1923_2,cycle1923_3,cycle1923_4,cycle1923_5]⟩
lemma valid_data1923 : data1923.Valid src1923 dst1923 Finset.univ := by decide +kernel

def src1924 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1924 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1924_0 : CycleData E W := ⟨9,![0,17,16,6,2,13,12,11,8,18,4],![2,6,38,16,3,4,28,26,14,18,8]⟩
def cycle1924_1 : CycleData E W := ⟨9,![5,15,14,1,10,7,3,21,20,19,9],![2,16,26,6,4,14,3,8,28,38,18]⟩
def data1924 : PartitionData E W := ⟨2,![cycle1924_0,cycle1924_1]⟩
lemma valid_data1924 : data1924.Valid src1924 dst1924 Finset.univ := by decide +kernel

def src1925 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1925 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1925_0 : CycleData E W := ⟨9,![5,16,17,1,2,3,18,12,11,8,9],![2,16,38,6,4,3,8,28,26,14,18]⟩
def cycle1925_1 : CycleData E W := ⟨9,![0,14,15,6,7,10,13,19,20,21,4],![2,6,26,16,3,14,4,28,18,38,8]⟩
def data1925 : PartitionData E W := ⟨2,![cycle1925_0,cycle1925_1]⟩
lemma valid_data1925 : data1925.Valid src1925 dst1925 Finset.univ := by decide +kernel

def src1926 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1926 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1926_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1926_1 : CycleData E W := ⟨2,![1,17,16,13],![4,6,38,26]⟩
def cycle1926_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1926_3 : CycleData E W := ⟨4,![3,21,20,12,15,6],![3,8,38,28,26,16]⟩
def cycle1926_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1926_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data1926 : PartitionData E W := ⟨6,![cycle1926_0,cycle1926_1,cycle1926_2,cycle1926_3,cycle1926_4,cycle1926_5]⟩
lemma valid_data1926 : data1926.Valid src1926 dst1926 Finset.univ := by decide +kernel

def src1927 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1927 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1927_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1927_1 : CycleData E W := ⟨2,![1,17,16,13],![4,6,38,26]⟩
def cycle1927_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1927_3 : CycleData E W := ⟨3,![3,21,12,15,6],![3,8,28,26,16]⟩
def cycle1927_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1927_5 : CycleData E W := ⟨2,![8,19,20,11],![14,18,38,28]⟩
def data1927 : PartitionData E W := ⟨6,![cycle1927_0,cycle1927_1,cycle1927_2,cycle1927_3,cycle1927_4,cycle1927_5]⟩
lemma valid_data1927 : data1927.Valid src1927 dst1927 Finset.univ := by decide +kernel

def src1928 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1928 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1928_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1928_1 : CycleData E W := ⟨2,![1,17,16,13],![4,6,38,26]⟩
def cycle1928_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1928_3 : CycleData E W := ⟨3,![3,18,12,15,6],![3,8,28,26,16]⟩
def cycle1928_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1928_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data1928 : PartitionData E W := ⟨6,![cycle1928_0,cycle1928_1,cycle1928_2,cycle1928_3,cycle1928_4,cycle1928_5]⟩
lemma valid_data1928 : data1928.Valid src1928 dst1928 Finset.univ := by decide +kernel

def src1929 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1929 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1929_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1929_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1929_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1929_3 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1929_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1929_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1929_6 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1929 : PartitionData E W := ⟨7,![cycle1929_0,cycle1929_1,cycle1929_2,cycle1929_3,cycle1929_4,cycle1929_5,cycle1929_6]⟩
lemma valid_data1929 : data1929.Valid src1929 dst1929 Finset.univ := by decide +kernel

def src1930 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1930 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1930_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1930_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1930_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1930_3 : CycleData E W := ⟨4,![4,3,6,15,19,9],![2,8,3,16,38,18]⟩
def cycle1930_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle1930_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1930 : PartitionData E W := ⟨6,![cycle1930_0,cycle1930_1,cycle1930_2,cycle1930_3,cycle1930_4,cycle1930_5]⟩
lemma valid_data1930 : data1930.Valid src1930 dst1930 Finset.univ := by decide +kernel

def src1931 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1931 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1931_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1931_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1931_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1931_3 : CycleData E W := ⟨4,![3,18,12,16,15,6],![3,8,28,26,38,16]⟩
def cycle1931_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1931_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data1931 : PartitionData E W := ⟨6,![cycle1931_0,cycle1931_1,cycle1931_2,cycle1931_3,cycle1931_4,cycle1931_5]⟩
lemma valid_data1931 : data1931.Valid src1931 dst1931 Finset.univ := by decide +kernel

def src1932 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1932 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1932_0 : CycleData E W := ⟨3,![0,1,13,15,5],![2,6,4,26,16]⟩
def cycle1932_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1932_2 : CycleData E W := ⟨2,![3,21,16,6],![3,8,38,16]⟩
def cycle1932_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1932_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1932_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1932 : PartitionData E W := ⟨6,![cycle1932_0,cycle1932_1,cycle1932_2,cycle1932_3,cycle1932_4,cycle1932_5]⟩
lemma valid_data1932 : data1932.Valid src1932 dst1932 Finset.univ := by decide +kernel

def src1933 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1933 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1933_0 : CycleData E W := ⟨2,![0,17,16,5],![2,6,38,16]⟩
def cycle1933_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1933_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1933_3 : CycleData E W := ⟨3,![3,21,12,15,6],![3,8,28,26,16]⟩
def cycle1933_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1933_5 : CycleData E W := ⟨2,![8,19,20,11],![14,18,38,28]⟩
def data1933 : PartitionData E W := ⟨6,![cycle1933_0,cycle1933_1,cycle1933_2,cycle1933_3,cycle1933_4,cycle1933_5]⟩
lemma valid_data1933 : data1933.Valid src1933 dst1933 Finset.univ := by decide +kernel

def src1934 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1934 : E → W := ![6,4,3,8,2,16,3,14,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1934_0 : CycleData E W := ⟨2,![0,17,16,5],![2,6,38,16]⟩
def cycle1934_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1934_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1934_3 : CycleData E W := ⟨3,![3,18,12,15,6],![3,8,28,26,16]⟩
def cycle1934_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1934_5 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def data1934 : PartitionData E W := ⟨6,![cycle1934_0,cycle1934_1,cycle1934_2,cycle1934_3,cycle1934_4,cycle1934_5]⟩
lemma valid_data1934 : data1934.Valid src1934 dst1934 Finset.univ := by decide +kernel

def src1935 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1935 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1935_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1935_1 : CycleData E W := ⟨2,![1,17,16,10],![4,6,38,26]⟩
def cycle1935_2 : CycleData E W := ⟨3,![2,13,20,21,3],![3,4,28,38,8]⟩
def cycle1935_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1935_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1935_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1935 : PartitionData E W := ⟨6,![cycle1935_0,cycle1935_1,cycle1935_2,cycle1935_3,cycle1935_4,cycle1935_5]⟩
lemma valid_data1935 : data1935.Valid src1935 dst1935 Finset.univ := by decide +kernel

def src1936 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1936 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1936_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1936_1 : CycleData E W := ⟨2,![1,17,16,10],![4,6,38,26]⟩
def cycle1936_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1936_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1936_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1936_5 : CycleData E W := ⟨2,![8,19,20,12],![14,18,38,28]⟩
def data1936 : PartitionData E W := ⟨6,![cycle1936_0,cycle1936_1,cycle1936_2,cycle1936_3,cycle1936_4,cycle1936_5]⟩
lemma valid_data1936 : data1936.Valid src1936 dst1936 Finset.univ := by decide +kernel

def src1937 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1937 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1937_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1937_1 : CycleData E W := ⟨2,![1,17,16,10],![4,6,38,26]⟩
def cycle1937_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1937_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1937_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1937_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1937 : PartitionData E W := ⟨6,![cycle1937_0,cycle1937_1,cycle1937_2,cycle1937_3,cycle1937_4,cycle1937_5]⟩
lemma valid_data1937 : data1937.Valid src1937 dst1937 Finset.univ := by decide +kernel

def src1938 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1938 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1938_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1938_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1938_2 : CycleData E W := ⟨2,![2,13,12,7],![3,4,28,14]⟩
def cycle1938_3 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1938_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1938_5 : CycleData E W := ⟨3,![8,19,20,16,11],![14,18,28,38,26]⟩
def data1938 : PartitionData E W := ⟨6,![cycle1938_0,cycle1938_1,cycle1938_2,cycle1938_3,cycle1938_4,cycle1938_5]⟩
lemma valid_data1938 : data1938.Valid src1938 dst1938 Finset.univ := by decide +kernel

def src1939 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1939 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1939_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1939_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1939_2 : CycleData E W := ⟨2,![2,13,12,7],![3,4,28,14]⟩
def cycle1939_3 : CycleData E W := ⟨3,![3,21,20,15,6],![3,8,28,38,16]⟩
def cycle1939_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1939_5 : CycleData E W := ⟨2,![8,19,16,11],![14,18,38,26]⟩
def data1939 : PartitionData E W := ⟨6,![cycle1939_0,cycle1939_1,cycle1939_2,cycle1939_3,cycle1939_4,cycle1939_5]⟩
lemma valid_data1939 : data1939.Valid src1939 dst1939 Finset.univ := by decide +kernel

def src1940 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1940 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1940_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1940_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1940_2 : CycleData E W := ⟨2,![2,13,12,7],![3,4,28,14]⟩
def cycle1940_3 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1940_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1940_5 : CycleData E W := ⟨2,![8,20,16,11],![14,18,38,26]⟩
def data1940 : PartitionData E W := ⟨6,![cycle1940_0,cycle1940_1,cycle1940_2,cycle1940_3,cycle1940_4,cycle1940_5]⟩
lemma valid_data1940 : data1940.Valid src1940 dst1940 Finset.univ := by decide +kernel

def src1941 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1941 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1941_0 : CycleData E W := ⟨2,![0,14,15,5],![2,6,26,16]⟩
def cycle1941_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1941_2 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle1941_3 : CycleData E W := ⟨2,![3,21,16,6],![3,8,38,16]⟩
def cycle1941_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1941_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1941 : PartitionData E W := ⟨6,![cycle1941_0,cycle1941_1,cycle1941_2,cycle1941_3,cycle1941_4,cycle1941_5]⟩
lemma valid_data1941 : data1941.Valid src1941 dst1941 Finset.univ := by decide +kernel

def src1942 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1942 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1942_0 : CycleData E W := ⟨2,![0,17,16,5],![2,6,38,16]⟩
def cycle1942_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1942_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1942_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1942_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1942_5 : CycleData E W := ⟨2,![8,19,20,12],![14,18,38,28]⟩
def data1942 : PartitionData E W := ⟨6,![cycle1942_0,cycle1942_1,cycle1942_2,cycle1942_3,cycle1942_4,cycle1942_5]⟩
lemma valid_data1942 : data1942.Valid src1942 dst1942 Finset.univ := by decide +kernel

def src1943 : E → W := ![2,6,4,3,8,2,16,3,14,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1943 : E → W := ![6,4,3,8,2,16,3,14,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1943_0 : CycleData E W := ⟨2,![0,17,16,5],![2,6,38,16]⟩
def cycle1943_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1943_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1943_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1943_4 : CycleData E W := ⟨2,![6,15,11,7],![3,16,26,14]⟩
def cycle1943_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1943 : PartitionData E W := ⟨6,![cycle1943_0,cycle1943_1,cycle1943_2,cycle1943_3,cycle1943_4,cycle1943_5]⟩
lemma valid_data1943 : data1943.Valid src1943 dst1943 Finset.univ := by decide +kernel

def lookupB9 (j : ℕ) : PartitionData E W := (if j < 72 then (if j < 36 then (if j < 18 then (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then data1800 else data1801) else (if j < 3 then data1802 else data1803)) else (if j < 6 then (if j < 5 then data1804 else data1805) else (if j < 7 then data1806 else (if j < 8 then data1807 else data1808)))) else (if j < 13 then (if j < 11 then (if j < 10 then data1809 else data1810) else (if j < 12 then data1811 else data1812)) else (if j < 15 then (if j < 14 then data1813 else data1814) else (if j < 16 then data1815 else (if j < 17 then data1816 else data1817))))) else (if j < 27 then (if j < 22 then (if j < 20 then (if j < 19 then data1818 else data1819) else (if j < 21 then data1820 else data1821)) else (if j < 24 then (if j < 23 then data1822 else data1823) else (if j < 25 then data1824 else (if j < 26 then data1825 else data1826)))) else (if j < 31 then (if j < 29 then (if j < 28 then data1827 else data1828) else (if j < 30 then data1829 else data1830)) else (if j < 33 then (if j < 32 then data1831 else data1832) else (if j < 34 then data1833 else (if j < 35 then data1834 else data1835)))))) else (if j < 54 then (if j < 45 then (if j < 40 then (if j < 38 then (if j < 37 then data1836 else data1837) else (if j < 39 then data1838 else data1839)) else (if j < 42 then (if j < 41 then data1840 else data1841) else (if j < 43 then data1842 else (if j < 44 then data1843 else data1844)))) else (if j < 49 then (if j < 47 then (if j < 46 then data1845 else data1846) else (if j < 48 then data1847 else data1848)) else (if j < 51 then (if j < 50 then data1849 else data1850) else (if j < 52 then data1851 else (if j < 53 then data1852 else data1853))))) else (if j < 63 then (if j < 58 then (if j < 56 then (if j < 55 then data1854 else data1855) else (if j < 57 then data1856 else data1857)) else (if j < 60 then (if j < 59 then data1858 else data1859) else (if j < 61 then data1860 else (if j < 62 then data1861 else data1862)))) else (if j < 67 then (if j < 65 then (if j < 64 then data1863 else data1864) else (if j < 66 then data1865 else data1866)) else (if j < 69 then (if j < 68 then data1867 else data1868) else (if j < 70 then data1869 else (if j < 71 then data1870 else data1871))))))) else (if j < 108 then (if j < 90 then (if j < 81 then (if j < 76 then (if j < 74 then (if j < 73 then data1872 else data1873) else (if j < 75 then data1874 else data1875)) else (if j < 78 then (if j < 77 then data1876 else data1877) else (if j < 79 then data1878 else (if j < 80 then data1879 else data1880)))) else (if j < 85 then (if j < 83 then (if j < 82 then data1881 else data1882) else (if j < 84 then data1883 else data1884)) else (if j < 87 then (if j < 86 then data1885 else data1886) else (if j < 88 then data1887 else (if j < 89 then data1888 else data1889))))) else (if j < 99 then (if j < 94 then (if j < 92 then (if j < 91 then data1890 else data1891) else (if j < 93 then data1892 else data1893)) else (if j < 96 then (if j < 95 then data1894 else data1895) else (if j < 97 then data1896 else (if j < 98 then data1897 else data1898)))) else (if j < 103 then (if j < 101 then (if j < 100 then data1899 else data1900) else (if j < 102 then data1901 else data1902)) else (if j < 105 then (if j < 104 then data1903 else data1904) else (if j < 106 then data1905 else (if j < 107 then data1906 else data1907)))))) else (if j < 126 then (if j < 117 then (if j < 112 then (if j < 110 then (if j < 109 then data1908 else data1909) else (if j < 111 then data1910 else data1911)) else (if j < 114 then (if j < 113 then data1912 else data1913) else (if j < 115 then data1914 else (if j < 116 then data1915 else data1916)))) else (if j < 121 then (if j < 119 then (if j < 118 then data1917 else data1918) else (if j < 120 then data1919 else data1920)) else (if j < 123 then (if j < 122 then data1921 else data1922) else (if j < 124 then data1923 else (if j < 125 then data1924 else data1925))))) else (if j < 135 then (if j < 130 then (if j < 128 then (if j < 127 then data1926 else data1927) else (if j < 129 then data1928 else data1929)) else (if j < 132 then (if j < 131 then data1930 else data1931) else (if j < 133 then data1932 else (if j < 134 then data1933 else data1934)))) else (if j < 139 then (if j < 137 then (if j < 136 then data1935 else data1936) else (if j < 138 then data1937 else data1938)) else (if j < 141 then (if j < 140 then data1939 else data1940) else (if j < 142 then data1941 else (if j < 143 then data1942 else data1943))))))))

def srcTableB9 (j : ℕ) : E → W := (if j < 72 then (if j < 36 then (if j < 18 then (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then src1800 else src1801) else (if j < 3 then src1802 else src1803)) else (if j < 6 then (if j < 5 then src1804 else src1805) else (if j < 7 then src1806 else (if j < 8 then src1807 else src1808)))) else (if j < 13 then (if j < 11 then (if j < 10 then src1809 else src1810) else (if j < 12 then src1811 else src1812)) else (if j < 15 then (if j < 14 then src1813 else src1814) else (if j < 16 then src1815 else (if j < 17 then src1816 else src1817))))) else (if j < 27 then (if j < 22 then (if j < 20 then (if j < 19 then src1818 else src1819) else (if j < 21 then src1820 else src1821)) else (if j < 24 then (if j < 23 then src1822 else src1823) else (if j < 25 then src1824 else (if j < 26 then src1825 else src1826)))) else (if j < 31 then (if j < 29 then (if j < 28 then src1827 else src1828) else (if j < 30 then src1829 else src1830)) else (if j < 33 then (if j < 32 then src1831 else src1832) else (if j < 34 then src1833 else (if j < 35 then src1834 else src1835)))))) else (if j < 54 then (if j < 45 then (if j < 40 then (if j < 38 then (if j < 37 then src1836 else src1837) else (if j < 39 then src1838 else src1839)) else (if j < 42 then (if j < 41 then src1840 else src1841) else (if j < 43 then src1842 else (if j < 44 then src1843 else src1844)))) else (if j < 49 then (if j < 47 then (if j < 46 then src1845 else src1846) else (if j < 48 then src1847 else src1848)) else (if j < 51 then (if j < 50 then src1849 else src1850) else (if j < 52 then src1851 else (if j < 53 then src1852 else src1853))))) else (if j < 63 then (if j < 58 then (if j < 56 then (if j < 55 then src1854 else src1855) else (if j < 57 then src1856 else src1857)) else (if j < 60 then (if j < 59 then src1858 else src1859) else (if j < 61 then src1860 else (if j < 62 then src1861 else src1862)))) else (if j < 67 then (if j < 65 then (if j < 64 then src1863 else src1864) else (if j < 66 then src1865 else src1866)) else (if j < 69 then (if j < 68 then src1867 else src1868) else (if j < 70 then src1869 else (if j < 71 then src1870 else src1871))))))) else (if j < 108 then (if j < 90 then (if j < 81 then (if j < 76 then (if j < 74 then (if j < 73 then src1872 else src1873) else (if j < 75 then src1874 else src1875)) else (if j < 78 then (if j < 77 then src1876 else src1877) else (if j < 79 then src1878 else (if j < 80 then src1879 else src1880)))) else (if j < 85 then (if j < 83 then (if j < 82 then src1881 else src1882) else (if j < 84 then src1883 else src1884)) else (if j < 87 then (if j < 86 then src1885 else src1886) else (if j < 88 then src1887 else (if j < 89 then src1888 else src1889))))) else (if j < 99 then (if j < 94 then (if j < 92 then (if j < 91 then src1890 else src1891) else (if j < 93 then src1892 else src1893)) else (if j < 96 then (if j < 95 then src1894 else src1895) else (if j < 97 then src1896 else (if j < 98 then src1897 else src1898)))) else (if j < 103 then (if j < 101 then (if j < 100 then src1899 else src1900) else (if j < 102 then src1901 else src1902)) else (if j < 105 then (if j < 104 then src1903 else src1904) else (if j < 106 then src1905 else (if j < 107 then src1906 else src1907)))))) else (if j < 126 then (if j < 117 then (if j < 112 then (if j < 110 then (if j < 109 then src1908 else src1909) else (if j < 111 then src1910 else src1911)) else (if j < 114 then (if j < 113 then src1912 else src1913) else (if j < 115 then src1914 else (if j < 116 then src1915 else src1916)))) else (if j < 121 then (if j < 119 then (if j < 118 then src1917 else src1918) else (if j < 120 then src1919 else src1920)) else (if j < 123 then (if j < 122 then src1921 else src1922) else (if j < 124 then src1923 else (if j < 125 then src1924 else src1925))))) else (if j < 135 then (if j < 130 then (if j < 128 then (if j < 127 then src1926 else src1927) else (if j < 129 then src1928 else src1929)) else (if j < 132 then (if j < 131 then src1930 else src1931) else (if j < 133 then src1932 else (if j < 134 then src1933 else src1934)))) else (if j < 139 then (if j < 137 then (if j < 136 then src1935 else src1936) else (if j < 138 then src1937 else src1938)) else (if j < 141 then (if j < 140 then src1939 else src1940) else (if j < 142 then src1941 else (if j < 143 then src1942 else src1943))))))))

def dstTableB9 (j : ℕ) : E → W := (if j < 72 then (if j < 36 then (if j < 18 then (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then dst1800 else dst1801) else (if j < 3 then dst1802 else dst1803)) else (if j < 6 then (if j < 5 then dst1804 else dst1805) else (if j < 7 then dst1806 else (if j < 8 then dst1807 else dst1808)))) else (if j < 13 then (if j < 11 then (if j < 10 then dst1809 else dst1810) else (if j < 12 then dst1811 else dst1812)) else (if j < 15 then (if j < 14 then dst1813 else dst1814) else (if j < 16 then dst1815 else (if j < 17 then dst1816 else dst1817))))) else (if j < 27 then (if j < 22 then (if j < 20 then (if j < 19 then dst1818 else dst1819) else (if j < 21 then dst1820 else dst1821)) else (if j < 24 then (if j < 23 then dst1822 else dst1823) else (if j < 25 then dst1824 else (if j < 26 then dst1825 else dst1826)))) else (if j < 31 then (if j < 29 then (if j < 28 then dst1827 else dst1828) else (if j < 30 then dst1829 else dst1830)) else (if j < 33 then (if j < 32 then dst1831 else dst1832) else (if j < 34 then dst1833 else (if j < 35 then dst1834 else dst1835)))))) else (if j < 54 then (if j < 45 then (if j < 40 then (if j < 38 then (if j < 37 then dst1836 else dst1837) else (if j < 39 then dst1838 else dst1839)) else (if j < 42 then (if j < 41 then dst1840 else dst1841) else (if j < 43 then dst1842 else (if j < 44 then dst1843 else dst1844)))) else (if j < 49 then (if j < 47 then (if j < 46 then dst1845 else dst1846) else (if j < 48 then dst1847 else dst1848)) else (if j < 51 then (if j < 50 then dst1849 else dst1850) else (if j < 52 then dst1851 else (if j < 53 then dst1852 else dst1853))))) else (if j < 63 then (if j < 58 then (if j < 56 then (if j < 55 then dst1854 else dst1855) else (if j < 57 then dst1856 else dst1857)) else (if j < 60 then (if j < 59 then dst1858 else dst1859) else (if j < 61 then dst1860 else (if j < 62 then dst1861 else dst1862)))) else (if j < 67 then (if j < 65 then (if j < 64 then dst1863 else dst1864) else (if j < 66 then dst1865 else dst1866)) else (if j < 69 then (if j < 68 then dst1867 else dst1868) else (if j < 70 then dst1869 else (if j < 71 then dst1870 else dst1871))))))) else (if j < 108 then (if j < 90 then (if j < 81 then (if j < 76 then (if j < 74 then (if j < 73 then dst1872 else dst1873) else (if j < 75 then dst1874 else dst1875)) else (if j < 78 then (if j < 77 then dst1876 else dst1877) else (if j < 79 then dst1878 else (if j < 80 then dst1879 else dst1880)))) else (if j < 85 then (if j < 83 then (if j < 82 then dst1881 else dst1882) else (if j < 84 then dst1883 else dst1884)) else (if j < 87 then (if j < 86 then dst1885 else dst1886) else (if j < 88 then dst1887 else (if j < 89 then dst1888 else dst1889))))) else (if j < 99 then (if j < 94 then (if j < 92 then (if j < 91 then dst1890 else dst1891) else (if j < 93 then dst1892 else dst1893)) else (if j < 96 then (if j < 95 then dst1894 else dst1895) else (if j < 97 then dst1896 else (if j < 98 then dst1897 else dst1898)))) else (if j < 103 then (if j < 101 then (if j < 100 then dst1899 else dst1900) else (if j < 102 then dst1901 else dst1902)) else (if j < 105 then (if j < 104 then dst1903 else dst1904) else (if j < 106 then dst1905 else (if j < 107 then dst1906 else dst1907)))))) else (if j < 126 then (if j < 117 then (if j < 112 then (if j < 110 then (if j < 109 then dst1908 else dst1909) else (if j < 111 then dst1910 else dst1911)) else (if j < 114 then (if j < 113 then dst1912 else dst1913) else (if j < 115 then dst1914 else (if j < 116 then dst1915 else dst1916)))) else (if j < 121 then (if j < 119 then (if j < 118 then dst1917 else dst1918) else (if j < 120 then dst1919 else dst1920)) else (if j < 123 then (if j < 122 then dst1921 else dst1922) else (if j < 124 then dst1923 else (if j < 125 then dst1924 else dst1925))))) else (if j < 135 then (if j < 130 then (if j < 128 then (if j < 127 then dst1926 else dst1927) else (if j < 129 then dst1928 else dst1929)) else (if j < 132 then (if j < 131 then dst1930 else dst1931) else (if j < 133 then dst1932 else (if j < 134 then dst1933 else dst1934)))) else (if j < 139 then (if j < 137 then (if j < 136 then dst1935 else dst1936) else (if j < 138 then dst1937 else dst1938)) else (if j < 141 then (if j < 140 then dst1939 else dst1940) else (if j < 142 then dst1941 else (if j < 143 then dst1942 else dst1943))))))))

def caseB9 (i : Fin 144) : Cases := ⟨1800 + i.val,by have := i.isLt; omega⟩
lemma tableB9_valid (i : Fin 144) :
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

lemma srcB9_row : ∀ (i : Fin 144) (e : E),
    srcTableB9 i.val e = caseSource (caseB9 i) e := by decide +kernel

lemma dstB9_row : ∀ (i : Fin 144) (e : E),
    dstTableB9 i.val e = caseTarget (caseB9 i) e := by decide +kernel

lemma sizeB9 : ∀ i : Fin 144, (lookupB9 i.val).size ≤ 5 →
    (lookupB9 i.val).size = 2 ∧
      (⟨caseKey (caseB9 i),caseKey_lt (caseB9 i)⟩ : Fin 3888) ∈ good := by decide +kernel
lemma certificateB9 (i : Fin 144) : Certificate (caseB9 i) := by
  refine ⟨lookupB9 i.val,?_,sizeB9 i⟩
  have hv := tableB9_valid i
  rw [funext (srcB9_row i),funext (dstB9_row i)] at hv
  exact hv
lemma certificateInterval9 : FiniteIntervals.Covers CertificateAt 1800 1944 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 1800 144 (fun i _ => certificateB9 i)
#print axioms certificateInterval9
end Erdos184Work.FiveRows1

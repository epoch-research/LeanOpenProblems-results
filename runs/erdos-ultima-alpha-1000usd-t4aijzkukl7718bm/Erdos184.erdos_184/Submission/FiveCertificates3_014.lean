import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src2800 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst2800 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2800_0 : CycleData E W := ⟨3,![0,15,14,3,4],![2,6,27,4,8]⟩
def cycle2800_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2800_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2800_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,26,16]⟩
def cycle2800_4 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,27,28]⟩
def cycle2800_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2800 : PartitionData E W := ⟨6,![cycle2800_0,cycle2800_1,cycle2800_2,cycle2800_3,cycle2800_4,cycle2800_5]⟩
lemma valid_data2800 : data2800.Valid src2800 dst2800 Finset.univ := by decide +kernel

def src2801 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst2801 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2801_0 : CycleData E W := ⟨3,![0,15,14,3,4],![2,6,27,4,8]⟩
def cycle2801_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2801_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2801_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,26,16]⟩
def cycle2801_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2801_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,26,38]⟩
def data2801 : PartitionData E W := ⟨6,![cycle2801_0,cycle2801_1,cycle2801_2,cycle2801_3,cycle2801_4,cycle2801_5]⟩
lemma valid_data2801 : data2801.Valid src2801 dst2801 Finset.univ := by decide +kernel

def src2802 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst2802 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2802_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2802_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2802_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,27,14]⟩
def cycle2802_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2802_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2802_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2802 : PartitionData E W := ⟨6,![cycle2802_0,cycle2802_1,cycle2802_2,cycle2802_3,cycle2802_4,cycle2802_5]⟩
lemma valid_data2802 : data2802.Valid src2802 dst2802 Finset.univ := by decide +kernel

def src2803 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst2803 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2803_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2803_1 : CycleData E W := ⟨4,![2,10,11,18,21,7],![3,4,14,27,38,18]⟩
def cycle2803_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2803_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2803_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2803_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2803 : PartitionData E W := ⟨6,![cycle2803_0,cycle2803_1,cycle2803_2,cycle2803_3,cycle2803_4,cycle2803_5]⟩
lemma valid_data2803 : data2803.Valid src2803 dst2803 Finset.univ := by decide +kernel

def src2804 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst2804 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2804_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,6,3,18,16]⟩
def cycle2804_1 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2804_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2804_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle2804_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2804_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2804 : PartitionData E W := ⟨6,![cycle2804_0,cycle2804_1,cycle2804_2,cycle2804_3,cycle2804_4,cycle2804_5]⟩
lemma valid_data2804 : data2804.Valid src2804 dst2804 Finset.univ := by decide +kernel

def src2805 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst2805 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2805_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2805_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2805_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2805_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2805_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle2805_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2805 : PartitionData E W := ⟨6,![cycle2805_0,cycle2805_1,cycle2805_2,cycle2805_3,cycle2805_4,cycle2805_5]⟩
lemma valid_data2805 : data2805.Valid src2805 dst2805 Finset.univ := by decide +kernel

def src2806 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst2806 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2806_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2806_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2806_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle2806_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2806_4 : CycleData E W := ⟨3,![10,11,18,22,14],![4,14,27,38,28]⟩
def cycle2806_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2806 : PartitionData E W := ⟨6,![cycle2806_0,cycle2806_1,cycle2806_2,cycle2806_3,cycle2806_4,cycle2806_5]⟩
lemma valid_data2806 : data2806.Valid src2806 dst2806 Finset.univ := by decide +kernel

def src2807 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst2807 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2807_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2807_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2807_2 : CycleData E W := ⟨3,![3,23,18,11,10],![4,8,38,27,14]⟩
def cycle2807_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle2807_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2807_5 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def data2807 : PartitionData E W := ⟨6,![cycle2807_0,cycle2807_1,cycle2807_2,cycle2807_3,cycle2807_4,cycle2807_5]⟩
lemma valid_data2807 : data2807.Valid src2807 dst2807 Finset.univ := by decide +kernel

def src2808 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst2808 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle2808_0 : CycleData E W := ⟨3,![0,15,14,3,4],![2,6,26,4,8]⟩
def cycle2808_1 : CycleData E W := ⟨3,![1,19,23,20,7],![3,6,38,8,18]⟩
def cycle2808_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2808_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,27,16]⟩
def cycle2808_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2808_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2808 : PartitionData E W := ⟨6,![cycle2808_0,cycle2808_1,cycle2808_2,cycle2808_3,cycle2808_4,cycle2808_5]⟩
lemma valid_data2808 : data2808.Valid src2808 dst2808 Finset.univ := by decide +kernel

def src2809 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst2809 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle2809_0 : CycleData E W := ⟨3,![0,15,14,3,4],![2,6,26,4,8]⟩
def cycle2809_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2809_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2809_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,27,16]⟩
def cycle2809_4 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,26,28]⟩
def cycle2809_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2809 : PartitionData E W := ⟨6,![cycle2809_0,cycle2809_1,cycle2809_2,cycle2809_3,cycle2809_4,cycle2809_5]⟩
lemma valid_data2809 : data2809.Valid src2809 dst2809 Finset.univ := by decide +kernel

def src2810 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst2810 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle2810_0 : CycleData E W := ⟨3,![0,15,14,3,4],![2,6,26,4,8]⟩
def cycle2810_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2810_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2810_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,27,16]⟩
def cycle2810_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2810_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,27,38]⟩
def data2810 : PartitionData E W := ⟨6,![cycle2810_0,cycle2810_1,cycle2810_2,cycle2810_3,cycle2810_4,cycle2810_5]⟩
lemma valid_data2810 : data2810.Valid src2810 dst2810 Finset.univ := by decide +kernel

def src2811 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst2811 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle2811_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2811_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2811_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2811_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2811_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle2811_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2811 : PartitionData E W := ⟨6,![cycle2811_0,cycle2811_1,cycle2811_2,cycle2811_3,cycle2811_4,cycle2811_5]⟩
lemma valid_data2811 : data2811.Valid src2811 dst2811 Finset.univ := by decide +kernel

def src2812 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst2812 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle2812_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2812_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2812_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle2812_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2812_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle2812_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2812 : PartitionData E W := ⟨6,![cycle2812_0,cycle2812_1,cycle2812_2,cycle2812_3,cycle2812_4,cycle2812_5]⟩
lemma valid_data2812 : data2812.Valid src2812 dst2812 Finset.univ := by decide +kernel

def src2813 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst2813 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle2813_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle2813_1 : CycleData E W := ⟨2,![1,19,11,6],![3,6,27,14]⟩
def cycle2813_2 : CycleData E W := ⟨3,![2,14,13,21,7],![3,4,26,28,18]⟩
def cycle2813_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle2813_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2813_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,27,38]⟩
def data2813 : PartitionData E W := ⟨6,![cycle2813_0,cycle2813_1,cycle2813_2,cycle2813_3,cycle2813_4,cycle2813_5]⟩
lemma valid_data2813 : data2813.Valid src2813 dst2813 Finset.univ := by decide +kernel

def src2814 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst2814 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle2814_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2814_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2814_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2814_3 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle2814_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle2814_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2814 : PartitionData E W := ⟨6,![cycle2814_0,cycle2814_1,cycle2814_2,cycle2814_3,cycle2814_4,cycle2814_5]⟩
lemma valid_data2814 : data2814.Valid src2814 dst2814 Finset.univ := by decide +kernel

def src2815 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst2815 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle2815_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2815_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2815_2 : CycleData E W := ⟨3,![4,23,12,18,9],![2,8,28,27,16]⟩
def cycle2815_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2815_4 : CycleData E W := ⟨3,![10,11,19,15,14],![4,14,27,6,26]⟩
def cycle2815_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2815 : PartitionData E W := ⟨6,![cycle2815_0,cycle2815_1,cycle2815_2,cycle2815_3,cycle2815_4,cycle2815_5]⟩
lemma valid_data2815 : data2815.Valid src2815 dst2815 Finset.univ := by decide +kernel

def src2816 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst2816 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle2816_0 : CycleData E W := ⟨3,![0,15,14,3,4],![2,6,26,4,8]⟩
def cycle2816_1 : CycleData E W := ⟨3,![1,19,12,21,7],![3,6,27,28,18]⟩
def cycle2816_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2816_3 : CycleData E W := ⟨2,![5,11,18,9],![2,14,27,16]⟩
def cycle2816_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2816_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data2816 : PartitionData E W := ⟨6,![cycle2816_0,cycle2816_1,cycle2816_2,cycle2816_3,cycle2816_4,cycle2816_5]⟩
lemma valid_data2816 : data2816.Valid src2816 dst2816 Finset.univ := by decide +kernel

def src2817 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst2817 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle2817_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,27,14]⟩
def cycle2817_1 : CycleData E W := ⟨3,![1,19,22,21,7],![3,6,38,28,18]⟩
def cycle2817_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2817_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,26]⟩
def cycle2817_4 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2817_5 : CycleData E W := ⟨2,![16,12,13,17],![16,27,28,26]⟩
def data2817 : PartitionData E W := ⟨6,![cycle2817_0,cycle2817_1,cycle2817_2,cycle2817_3,cycle2817_4,cycle2817_5]⟩
lemma valid_data2817 : data2817.Valid src2817 dst2817 Finset.univ := by decide +kernel

def src2818 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst2818 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle2818_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,27,14]⟩
def cycle2818_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2818_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2818_3 : CycleData E W := ⟨3,![4,3,14,17,9],![2,8,4,26,16]⟩
def cycle2818_4 : CycleData E W := ⟨3,![20,8,16,12,23],![8,18,16,27,28]⟩
def cycle2818_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2818 : PartitionData E W := ⟨6,![cycle2818_0,cycle2818_1,cycle2818_2,cycle2818_3,cycle2818_4,cycle2818_5]⟩
lemma valid_data2818 : data2818.Valid src2818 dst2818 Finset.univ := by decide +kernel

def src2819 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst2819 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle2819_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,27,14]⟩
def cycle2819_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2819_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2819_3 : CycleData E W := ⟨3,![4,3,14,17,9],![2,8,4,26,16]⟩
def cycle2819_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,27]⟩
def cycle2819_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,26,38]⟩
def data2819 : PartitionData E W := ⟨6,![cycle2819_0,cycle2819_1,cycle2819_2,cycle2819_3,cycle2819_4,cycle2819_5]⟩
lemma valid_data2819 : data2819.Valid src2819 dst2819 Finset.univ := by decide +kernel

def src2820 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst2820 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle2820_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2820_1 : CycleData E W := ⟨3,![2,10,11,21,7],![3,4,14,28,18]⟩
def cycle2820_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2820_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2820_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle2820_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2820 : PartitionData E W := ⟨6,![cycle2820_0,cycle2820_1,cycle2820_2,cycle2820_3,cycle2820_4,cycle2820_5]⟩
lemma valid_data2820 : data2820.Valid src2820 dst2820 Finset.univ := by decide +kernel

def src2821 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst2821 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle2821_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2821_1 : CycleData E W := ⟨3,![2,14,18,21,7],![3,4,27,38,18]⟩
def cycle2821_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,14]⟩
def cycle2821_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2821_4 : CycleData E W := ⟨2,![15,12,22,19],![6,26,28,38]⟩
def cycle2821_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2821 : PartitionData E W := ⟨6,![cycle2821_0,cycle2821_1,cycle2821_2,cycle2821_3,cycle2821_4,cycle2821_5]⟩
lemma valid_data2821 : data2821.Valid src2821 dst2821 Finset.univ := by decide +kernel

def src2822 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst2822 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle2822_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,6,3,18,16]⟩
def cycle2822_1 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2822_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2822_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle2822_4 : CycleData E W := ⟨3,![15,12,21,22,19],![6,26,28,18,38]⟩
def cycle2822_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2822 : PartitionData E W := ⟨6,![cycle2822_0,cycle2822_1,cycle2822_2,cycle2822_3,cycle2822_4,cycle2822_5]⟩
lemma valid_data2822 : data2822.Valid src2822 dst2822 Finset.univ := by decide +kernel

def src2823 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst2823 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle2823_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2823_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2823_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2823_3 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,26]⟩
def cycle2823_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle2823_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2823 : PartitionData E W := ⟨6,![cycle2823_0,cycle2823_1,cycle2823_2,cycle2823_3,cycle2823_4,cycle2823_5]⟩
lemma valid_data2823 : data2823.Valid src2823 dst2823 Finset.univ := by decide +kernel

def src2824 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst2824 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle2824_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2824_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2824_2 : CycleData E W := ⟨3,![4,23,12,16,9],![2,8,28,26,16]⟩
def cycle2824_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2824_4 : CycleData E W := ⟨3,![10,11,22,18,14],![4,14,28,38,27]⟩
def cycle2824_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2824 : PartitionData E W := ⟨6,![cycle2824_0,cycle2824_1,cycle2824_2,cycle2824_3,cycle2824_4,cycle2824_5]⟩
lemma valid_data2824 : data2824.Valid src2824 dst2824 Finset.univ := by decide +kernel

def src2825 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst2825 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle2825_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2825_1 : CycleData E W := ⟨3,![2,10,11,21,7],![3,4,14,28,18]⟩
def cycle2825_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2825_3 : CycleData E W := ⟨3,![4,20,12,16,9],![2,8,28,26,16]⟩
def cycle2825_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2825_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2825 : PartitionData E W := ⟨6,![cycle2825_0,cycle2825_1,cycle2825_2,cycle2825_3,cycle2825_4,cycle2825_5]⟩
lemma valid_data2825 : data2825.Valid src2825 dst2825 Finset.univ := by decide +kernel

def src2826 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst2826 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle2826_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2826_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2826_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2826_3 : CycleData E W := ⟨2,![8,21,12,18],![16,18,28,27]⟩
def cycle2826_4 : CycleData E W := ⟨3,![10,11,22,16,14],![4,14,28,38,26]⟩
def cycle2826_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2826 : PartitionData E W := ⟨6,![cycle2826_0,cycle2826_1,cycle2826_2,cycle2826_3,cycle2826_4,cycle2826_5]⟩
lemma valid_data2826 : data2826.Valid src2826 dst2826 Finset.univ := by decide +kernel

def src2827 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst2827 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle2827_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2827_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2827_2 : CycleData E W := ⟨3,![4,23,12,18,9],![2,8,28,27,16]⟩
def cycle2827_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2827_4 : CycleData E W := ⟨3,![10,11,22,16,14],![4,14,28,38,26]⟩
def cycle2827_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2827 : PartitionData E W := ⟨6,![cycle2827_0,cycle2827_1,cycle2827_2,cycle2827_3,cycle2827_4,cycle2827_5]⟩
lemma valid_data2827 : data2827.Valid src2827 dst2827 Finset.univ := by decide +kernel

def src2828 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst2828 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle2828_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2828_1 : CycleData E W := ⟨3,![2,10,11,21,7],![3,4,14,28,18]⟩
def cycle2828_2 : CycleData E W := ⟨2,![3,23,16,14],![4,8,38,26]⟩
def cycle2828_3 : CycleData E W := ⟨3,![4,20,12,18,9],![2,8,28,27,16]⟩
def cycle2828_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2828_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2828 : PartitionData E W := ⟨6,![cycle2828_0,cycle2828_1,cycle2828_2,cycle2828_3,cycle2828_4,cycle2828_5]⟩
lemma valid_data2828 : data2828.Valid src2828 dst2828 Finset.univ := by decide +kernel

def src2829 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst2829 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle2829_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2829_1 : CycleData E W := ⟨3,![2,10,11,21,7],![3,4,14,28,18]⟩
def cycle2829_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,26]⟩
def cycle2829_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2829_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle2829_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2829 : PartitionData E W := ⟨6,![cycle2829_0,cycle2829_1,cycle2829_2,cycle2829_3,cycle2829_4,cycle2829_5]⟩
lemma valid_data2829 : data2829.Valid src2829 dst2829 Finset.univ := by decide +kernel

def src2830 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst2830 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle2830_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2830_1 : CycleData E W := ⟨3,![2,14,18,21,7],![3,4,26,38,18]⟩
def cycle2830_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,14]⟩
def cycle2830_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2830_4 : CycleData E W := ⟨2,![15,12,22,19],![6,27,28,38]⟩
def cycle2830_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2830 : PartitionData E W := ⟨6,![cycle2830_0,cycle2830_1,cycle2830_2,cycle2830_3,cycle2830_4,cycle2830_5]⟩
lemma valid_data2830 : data2830.Valid src2830 dst2830 Finset.univ := by decide +kernel

def src2831 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst2831 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle2831_0 : CycleData E W := ⟨3,![0,1,7,8,9],![2,6,3,18,16]⟩
def cycle2831_1 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle2831_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,26]⟩
def cycle2831_3 : CycleData E W := ⟨2,![4,20,11,5],![2,8,28,14]⟩
def cycle2831_4 : CycleData E W := ⟨3,![15,12,21,22,19],![6,27,28,18,38]⟩
def cycle2831_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2831 : PartitionData E W := ⟨6,![cycle2831_0,cycle2831_1,cycle2831_2,cycle2831_3,cycle2831_4,cycle2831_5]⟩
lemma valid_data2831 : data2831.Valid src2831 dst2831 Finset.univ := by decide +kernel

def src2832 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst2832 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle2832_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2832_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2832_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle2832_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2832_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,26,14,27]⟩
def cycle2832_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2832 : PartitionData E W := ⟨6,![cycle2832_0,cycle2832_1,cycle2832_2,cycle2832_3,cycle2832_4,cycle2832_5]⟩
lemma valid_data2832 : data2832.Valid src2832 dst2832 Finset.univ := by decide +kernel

def src2833 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst2833 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle2833_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2833_1 : CycleData E W := ⟨3,![2,10,17,21,7],![3,4,26,38,18]⟩
def cycle2833_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2833_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2833_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,26,14,27]⟩
def cycle2833_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2833 : PartitionData E W := ⟨6,![cycle2833_0,cycle2833_1,cycle2833_2,cycle2833_3,cycle2833_4,cycle2833_5]⟩
lemma valid_data2833 : data2833.Valid src2833 dst2833 Finset.univ := by decide +kernel

def src2834 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst2834 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle2834_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2834_1 : CycleData E W := ⟨2,![1,19,12,6],![3,6,27,14]⟩
def cycle2834_2 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2834_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2834_4 : CycleData E W := ⟨3,![4,23,17,11,5],![2,8,38,26,14]⟩
def cycle2834_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2834 : PartitionData E W := ⟨6,![cycle2834_0,cycle2834_1,cycle2834_2,cycle2834_3,cycle2834_4,cycle2834_5]⟩
lemma valid_data2834 : data2834.Valid src2834 dst2834 Finset.univ := by decide +kernel

def src2835 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst2835 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle2835_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2835_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2835_2 : CycleData E W := ⟨3,![4,23,19,15,9],![2,8,38,6,16]⟩
def cycle2835_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2835_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2835_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2835 : PartitionData E W := ⟨6,![cycle2835_0,cycle2835_1,cycle2835_2,cycle2835_3,cycle2835_4,cycle2835_5]⟩
lemma valid_data2835 : data2835.Valid src2835 dst2835 Finset.univ := by decide +kernel

def src2836 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst2836 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle2836_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2836_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2836_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle2836_3 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2836_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2836_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2836 : PartitionData E W := ⟨6,![cycle2836_0,cycle2836_1,cycle2836_2,cycle2836_3,cycle2836_4,cycle2836_5]⟩
lemma valid_data2836 : data2836.Valid src2836 dst2836 Finset.univ := by decide +kernel

def src2837 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst2837 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle2837_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2837_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2837_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2837_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,27,16]⟩
def cycle2837_4 : CycleData E W := ⟨2,![15,8,22,19],![6,16,18,38]⟩
def cycle2837_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2837 : PartitionData E W := ⟨6,![cycle2837_0,cycle2837_1,cycle2837_2,cycle2837_3,cycle2837_4,cycle2837_5]⟩
lemma valid_data2837 : data2837.Valid src2837 dst2837 Finset.univ := by decide +kernel

def src2838 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst2838 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle2838_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2838_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2838_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2838_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2838_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,27,14,26]⟩
def cycle2838_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2838 : PartitionData E W := ⟨6,![cycle2838_0,cycle2838_1,cycle2838_2,cycle2838_3,cycle2838_4,cycle2838_5]⟩
lemma valid_data2838 : data2838.Valid src2838 dst2838 Finset.univ := by decide +kernel

def src2839 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst2839 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle2839_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2839_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,26,38,18]⟩
def cycle2839_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2839_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2839_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,27,14,26]⟩
def cycle2839_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2839 : PartitionData E W := ⟨6,![cycle2839_0,cycle2839_1,cycle2839_2,cycle2839_3,cycle2839_4,cycle2839_5]⟩
lemma valid_data2839 : data2839.Valid src2839 dst2839 Finset.univ := by decide +kernel

def src2840 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst2840 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle2840_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2840_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2840_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2840_3 : CycleData E W := ⟨3,![4,23,17,12,5],![2,8,38,27,14]⟩
def cycle2840_4 : CycleData E W := ⟨3,![6,11,18,22,7],![3,14,26,38,18]⟩
def cycle2840_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2840 : PartitionData E W := ⟨6,![cycle2840_0,cycle2840_1,cycle2840_2,cycle2840_3,cycle2840_4,cycle2840_5]⟩
lemma valid_data2840 : data2840.Valid src2840 dst2840 Finset.univ := by decide +kernel

def src2841 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst2841 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle2841_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2841_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2841_2 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle2841_3 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,27]⟩
def cycle2841_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle2841_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2841 : PartitionData E W := ⟨6,![cycle2841_0,cycle2841_1,cycle2841_2,cycle2841_3,cycle2841_4,cycle2841_5]⟩
lemma valid_data2841 : data2841.Valid src2841 dst2841 Finset.univ := by decide +kernel

def src2842 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst2842 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle2842_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2842_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2842_2 : CycleData E W := ⟨4,![4,23,13,19,15,9],![2,8,28,27,6,16]⟩
def cycle2842_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2842_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle2842_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2842 : PartitionData E W := ⟨6,![cycle2842_0,cycle2842_1,cycle2842_2,cycle2842_3,cycle2842_4,cycle2842_5]⟩
lemma valid_data2842 : data2842.Valid src2842 dst2842 Finset.univ := by decide +kernel

def src2843 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst2843 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle2843_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2843_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2843_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,26]⟩
def cycle2843_3 : CycleData E W := ⟨4,![4,20,13,19,15,9],![2,8,28,27,6,16]⟩
def cycle2843_4 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2843_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2843 : PartitionData E W := ⟨6,![cycle2843_0,cycle2843_1,cycle2843_2,cycle2843_3,cycle2843_4,cycle2843_5]⟩
lemma valid_data2843 : data2843.Valid src2843 dst2843 Finset.univ := by decide +kernel

def src2844 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2844 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2844_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2844_1 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2844_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2844_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2844_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2844_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2844 : PartitionData E W := ⟨6,![cycle2844_0,cycle2844_1,cycle2844_2,cycle2844_3,cycle2844_4,cycle2844_5]⟩
lemma valid_data2844 : data2844.Valid src2844 dst2844 Finset.univ := by decide +kernel

def src2845 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2845 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2845_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2845_1 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2845_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2845_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2845_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2845_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2845 : PartitionData E W := ⟨6,![cycle2845_0,cycle2845_1,cycle2845_2,cycle2845_3,cycle2845_4,cycle2845_5]⟩
lemma valid_data2845 : data2845.Valid src2845 dst2845 Finset.univ := by decide +kernel

def src2846 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2846 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2846_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2846_1 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2846_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2846_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2846_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2846_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2846 : PartitionData E W := ⟨6,![cycle2846_0,cycle2846_1,cycle2846_2,cycle2846_3,cycle2846_4,cycle2846_5]⟩
lemma valid_data2846 : data2846.Valid src2846 dst2846 Finset.univ := by decide +kernel

def src2847 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2847 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2847_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2847_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2847_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2847_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2847_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle2847_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2847 : PartitionData E W := ⟨6,![cycle2847_0,cycle2847_1,cycle2847_2,cycle2847_3,cycle2847_4,cycle2847_5]⟩
lemma valid_data2847 : data2847.Valid src2847 dst2847 Finset.univ := by decide +kernel

def src2848 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2848 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2848_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2848_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2848_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle2848_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2848_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle2848_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2848 : PartitionData E W := ⟨6,![cycle2848_0,cycle2848_1,cycle2848_2,cycle2848_3,cycle2848_4,cycle2848_5]⟩
lemma valid_data2848 : data2848.Valid src2848 dst2848 Finset.univ := by decide +kernel

def src2849 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2849 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2849_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2849_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2849_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2849_3 : CycleData E W := ⟨3,![4,20,13,18,9],![2,8,28,27,16]⟩
def cycle2849_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2849_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2849 : PartitionData E W := ⟨6,![cycle2849_0,cycle2849_1,cycle2849_2,cycle2849_3,cycle2849_4,cycle2849_5]⟩
lemma valid_data2849 : data2849.Valid src2849 dst2849 Finset.univ := by decide +kernel

def src2850 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2850 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2850_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2850_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2850_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2850_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2850_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle2850_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2850 : PartitionData E W := ⟨6,![cycle2850_0,cycle2850_1,cycle2850_2,cycle2850_3,cycle2850_4,cycle2850_5]⟩
lemma valid_data2850 : data2850.Valid src2850 dst2850 Finset.univ := by decide +kernel

def src2851 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2851 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2851_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2851_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,26,38,18]⟩
def cycle2851_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2851_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2851_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle2851_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2851 : PartitionData E W := ⟨6,![cycle2851_0,cycle2851_1,cycle2851_2,cycle2851_3,cycle2851_4,cycle2851_5]⟩
lemma valid_data2851 : data2851.Valid src2851 dst2851 Finset.univ := by decide +kernel

def src2852 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2852 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2852_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,27,14]⟩
def cycle2852_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2852_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle2852_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2852_4 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,26,16]⟩
def cycle2852_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2852 : PartitionData E W := ⟨6,![cycle2852_0,cycle2852_1,cycle2852_2,cycle2852_3,cycle2852_4,cycle2852_5]⟩
lemma valid_data2852 : data2852.Valid src2852 dst2852 Finset.univ := by decide +kernel

def src2853 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst2853 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle2853_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2853_1 : CycleData E W := ⟨3,![2,10,17,8,7],![3,4,26,16,18]⟩
def cycle2853_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2853_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2853_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2853_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2853 : PartitionData E W := ⟨6,![cycle2853_0,cycle2853_1,cycle2853_2,cycle2853_3,cycle2853_4,cycle2853_5]⟩
lemma valid_data2853 : data2853.Valid src2853 dst2853 Finset.univ := by decide +kernel

def src2854 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst2854 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle2854_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2854_1 : CycleData E W := ⟨3,![2,10,17,8,7],![3,4,26,16,18]⟩
def cycle2854_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2854_3 : CycleData E W := ⟨3,![4,20,21,18,9],![2,8,18,38,16]⟩
def cycle2854_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2854_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2854 : PartitionData E W := ⟨6,![cycle2854_0,cycle2854_1,cycle2854_2,cycle2854_3,cycle2854_4,cycle2854_5]⟩
lemma valid_data2854 : data2854.Valid src2854 dst2854 Finset.univ := by decide +kernel

def src2855 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst2855 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle2855_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2855_1 : CycleData E W := ⟨3,![2,10,17,8,7],![3,4,26,16,18]⟩
def cycle2855_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2855_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2855_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2855_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2855 : PartitionData E W := ⟨6,![cycle2855_0,cycle2855_1,cycle2855_2,cycle2855_3,cycle2855_4,cycle2855_5]⟩
lemma valid_data2855 : data2855.Valid src2855 dst2855 Finset.univ := by decide +kernel

def src2856 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst2856 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle2856_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2856_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2856_2 : CycleData E W := ⟨3,![4,3,10,11,5],![2,8,4,26,14]⟩
def cycle2856_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2856_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle2856_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2856 : PartitionData E W := ⟨6,![cycle2856_0,cycle2856_1,cycle2856_2,cycle2856_3,cycle2856_4,cycle2856_5]⟩
lemma valid_data2856 : data2856.Valid src2856 dst2856 Finset.univ := by decide +kernel

def src2857 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst2857 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle2857_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2857_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2857_2 : CycleData E W := ⟨3,![4,3,10,11,5],![2,8,4,26,14]⟩
def cycle2857_3 : CycleData E W := ⟨3,![6,12,23,20,7],![3,14,28,8,18]⟩
def cycle2857_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle2857_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2857 : PartitionData E W := ⟨6,![cycle2857_0,cycle2857_1,cycle2857_2,cycle2857_3,cycle2857_4,cycle2857_5]⟩
lemma valid_data2857 : data2857.Valid src2857 dst2857 Finset.univ := by decide +kernel

def src2858 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst2858 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle2858_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2858_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2858_2 : CycleData E W := ⟨3,![4,3,10,11,5],![2,8,4,26,14]⟩
def cycle2858_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2858_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def cycle2858_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2858 : PartitionData E W := ⟨6,![cycle2858_0,cycle2858_1,cycle2858_2,cycle2858_3,cycle2858_4,cycle2858_5]⟩
lemma valid_data2858 : data2858.Valid src2858 dst2858 Finset.univ := by decide +kernel

def src2859 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst2859 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle2859_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2859_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2859_2 : CycleData E W := ⟨3,![4,23,19,15,9],![2,8,38,6,16]⟩
def cycle2859_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2859_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2859_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data2859 : PartitionData E W := ⟨6,![cycle2859_0,cycle2859_1,cycle2859_2,cycle2859_3,cycle2859_4,cycle2859_5]⟩
lemma valid_data2859 : data2859.Valid src2859 dst2859 Finset.univ := by decide +kernel

def src2860 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst2860 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle2860_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2860_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2860_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,27,16]⟩
def cycle2860_3 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2860_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2860_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data2860 : PartitionData E W := ⟨6,![cycle2860_0,cycle2860_1,cycle2860_2,cycle2860_3,cycle2860_4,cycle2860_5]⟩
lemma valid_data2860 : data2860.Valid src2860 dst2860 Finset.univ := by decide +kernel

def src2861 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst2861 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle2861_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2861_1 : CycleData E W := ⟨3,![1,19,18,11,6],![3,6,38,26,14]⟩
def cycle2861_2 : CycleData E W := ⟨3,![2,3,23,22,7],![3,4,8,38,18]⟩
def cycle2861_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2861_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2861_5 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def data2861 : PartitionData E W := ⟨6,![cycle2861_0,cycle2861_1,cycle2861_2,cycle2861_3,cycle2861_4,cycle2861_5]⟩
lemma valid_data2861 : data2861.Valid src2861 dst2861 Finset.univ := by decide +kernel

def src2862 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst2862 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle2862_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2862_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2862_2 : CycleData E W := ⟨3,![3,20,8,16,14],![4,8,18,16,27]⟩
def cycle2862_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle2862_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2862_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2862 : PartitionData E W := ⟨6,![cycle2862_0,cycle2862_1,cycle2862_2,cycle2862_3,cycle2862_4,cycle2862_5]⟩
lemma valid_data2862 : data2862.Valid src2862 dst2862 Finset.univ := by decide +kernel

def src2863 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst2863 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle2863_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2863_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2863_2 : CycleData E W := ⟨3,![3,20,8,16,14],![4,8,18,16,27]⟩
def cycle2863_3 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle2863_4 : CycleData E W := ⟨3,![6,11,18,21,7],![3,14,26,38,18]⟩
def cycle2863_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2863 : PartitionData E W := ⟨6,![cycle2863_0,cycle2863_1,cycle2863_2,cycle2863_3,cycle2863_4,cycle2863_5]⟩
lemma valid_data2863 : data2863.Valid src2863 dst2863 Finset.univ := by decide +kernel

def src2864 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst2864 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle2864_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2864_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2864_2 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle2864_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle2864_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2864_5 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def data2864 : PartitionData E W := ⟨6,![cycle2864_0,cycle2864_1,cycle2864_2,cycle2864_3,cycle2864_4,cycle2864_5]⟩
lemma valid_data2864 : data2864.Valid src2864 dst2864 Finset.univ := by decide +kernel

def src2865 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst2865 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle2865_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2865_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2865_2 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle2865_3 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,27]⟩
def cycle2865_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2865_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2865 : PartitionData E W := ⟨6,![cycle2865_0,cycle2865_1,cycle2865_2,cycle2865_3,cycle2865_4,cycle2865_5]⟩
lemma valid_data2865 : data2865.Valid src2865 dst2865 Finset.univ := by decide +kernel

def src2866 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst2866 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle2866_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2866_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2866_2 : CycleData E W := ⟨4,![4,23,13,19,15,9],![2,8,28,27,6,16]⟩
def cycle2866_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2866_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2866_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2866 : PartitionData E W := ⟨6,![cycle2866_0,cycle2866_1,cycle2866_2,cycle2866_3,cycle2866_4,cycle2866_5]⟩
lemma valid_data2866 : data2866.Valid src2866 dst2866 Finset.univ := by decide +kernel

def src2867 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst2867 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle2867_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2867_1 : CycleData E W := ⟨3,![1,19,13,12,6],![3,6,27,28,14]⟩
def cycle2867_2 : CycleData E W := ⟨3,![2,3,20,21,7],![3,4,8,28,18]⟩
def cycle2867_3 : CycleData E W := ⟨3,![4,23,17,11,5],![2,8,38,26,14]⟩
def cycle2867_4 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2867_5 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def data2867 : PartitionData E W := ⟨6,![cycle2867_0,cycle2867_1,cycle2867_2,cycle2867_3,cycle2867_4,cycle2867_5]⟩
lemma valid_data2867 : data2867.Valid src2867 dst2867 Finset.univ := by decide +kernel

def src2868 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2868 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2868_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2868_1 : CycleData E W := ⟨3,![1,19,23,3,2],![3,6,38,8,4]⟩
def cycle2868_2 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2868_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2868_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2868_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2868 : PartitionData E W := ⟨6,![cycle2868_0,cycle2868_1,cycle2868_2,cycle2868_3,cycle2868_4,cycle2868_5]⟩
lemma valid_data2868 : data2868.Valid src2868 dst2868 Finset.univ := by decide +kernel

def src2869 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2869 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2869_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2869_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2869_2 : CycleData E W := ⟨3,![2,3,23,12,6],![3,4,8,28,14]⟩
def cycle2869_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2869_4 : CycleData E W := ⟨2,![10,16,17,14],![4,26,16,27]⟩
def cycle2869_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2869 : PartitionData E W := ⟨6,![cycle2869_0,cycle2869_1,cycle2869_2,cycle2869_3,cycle2869_4,cycle2869_5]⟩
lemma valid_data2869 : data2869.Valid src2869 dst2869 Finset.univ := by decide +kernel

def src2870 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2870 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2870_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle2870_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2870_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle2870_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2870_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2870_5 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def data2870 : PartitionData E W := ⟨6,![cycle2870_0,cycle2870_1,cycle2870_2,cycle2870_3,cycle2870_4,cycle2870_5]⟩
lemma valid_data2870 : data2870.Valid src2870 dst2870 Finset.univ := by decide +kernel

def src2871 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst2871 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle2871_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2871_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2871_2 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2871_3 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def cycle2871_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2871_5 : CycleData E W := ⟨3,![15,11,12,22,19],![6,26,14,28,38]⟩
def data2871 : PartitionData E W := ⟨6,![cycle2871_0,cycle2871_1,cycle2871_2,cycle2871_3,cycle2871_4,cycle2871_5]⟩
lemma valid_data2871 : data2871.Valid src2871 dst2871 Finset.univ := by decide +kernel

def src2872 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst2872 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle2872_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2872_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2872_2 : CycleData E W := ⟨3,![4,23,13,17,9],![2,8,28,27,16]⟩
def cycle2872_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2872_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2872_5 : CycleData E W := ⟨3,![15,11,12,22,19],![6,26,14,28,38]⟩
def data2872 : PartitionData E W := ⟨6,![cycle2872_0,cycle2872_1,cycle2872_2,cycle2872_3,cycle2872_4,cycle2872_5]⟩
lemma valid_data2872 : data2872.Valid src2872 dst2872 Finset.univ := by decide +kernel

def src2873 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst2873 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle2873_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2873_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2873_2 : CycleData E W := ⟨3,![2,3,20,12,6],![3,4,8,28,14]⟩
def cycle2873_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2873_4 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def cycle2873_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data2873 : PartitionData E W := ⟨6,![cycle2873_0,cycle2873_1,cycle2873_2,cycle2873_3,cycle2873_4,cycle2873_5]⟩
lemma valid_data2873 : data2873.Valid src2873 dst2873 Finset.univ := by decide +kernel

def src2874 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2874 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2874_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2874_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2874_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2874_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2874_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2874_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data2874 : PartitionData E W := ⟨6,![cycle2874_0,cycle2874_1,cycle2874_2,cycle2874_3,cycle2874_4,cycle2874_5]⟩
lemma valid_data2874 : data2874.Valid src2874 dst2874 Finset.univ := by decide +kernel

def src2875 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2875 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2875_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2875_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2875_2 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle2875_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2875_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2875_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data2875 : PartitionData E W := ⟨6,![cycle2875_0,cycle2875_1,cycle2875_2,cycle2875_3,cycle2875_4,cycle2875_5]⟩
lemma valid_data2875 : data2875.Valid src2875 dst2875 Finset.univ := by decide +kernel

def src2876 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2876 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2876_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2876_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2876_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2876_3 : CycleData E W := ⟨3,![4,20,13,18,9],![2,8,28,27,16]⟩
def cycle2876_4 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2876_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2876 : PartitionData E W := ⟨6,![cycle2876_0,cycle2876_1,cycle2876_2,cycle2876_3,cycle2876_4,cycle2876_5]⟩
lemma valid_data2876 : data2876.Valid src2876 dst2876 Finset.univ := by decide +kernel

def src2877 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2877 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2877_0 : CycleData E W := ⟨10,![5,6,1,19,18,10,3,20,21,13,16,9],![2,14,3,6,38,26,4,8,18,28,27,16]⟩
def cycle2877_1 : CycleData E W := ⟨10,![0,15,14,2,7,8,17,11,12,22,23,4],![2,6,27,4,3,18,16,26,14,28,38,8]⟩
def data2877 : PartitionData E W := ⟨2,![cycle2877_0,cycle2877_1]⟩
lemma valid_data2877 : data2877.Valid src2877 dst2877 Finset.univ := by decide +kernel

def src2878 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2878 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2878_0 : CycleData E W := ⟨10,![0,1,2,3,20,21,18,11,12,13,16,9],![2,6,3,4,8,18,38,26,14,28,27,16]⟩
def cycle2878_1 : CycleData E W := ⟨10,![4,23,22,19,15,14,10,17,8,7,6,5],![2,8,28,38,6,27,4,26,16,18,3,14]⟩
def data2878 : PartitionData E W := ⟨2,![cycle2878_0,cycle2878_1]⟩
lemma valid_data2878 : data2878.Valid src2878 dst2878 Finset.univ := by decide +kernel

def src2879 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2879 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2879_0 : CycleData E W := ⟨10,![4,20,21,8,16,14,2,1,19,18,11,5],![2,8,28,18,16,27,4,3,6,38,26,14]⟩
def cycle2879_1 : CycleData E W := ⟨10,![0,15,13,12,6,7,22,23,3,10,17,9],![2,6,27,28,14,3,18,38,8,4,26,16]⟩
def data2879 : PartitionData E W := ⟨2,![cycle2879_0,cycle2879_1]⟩
lemma valid_data2879 : data2879.Valid src2879 dst2879 Finset.univ := by decide +kernel

def src2880 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst2880 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle2880_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2880_1 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2880_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2880_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2880_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2880_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data2880 : PartitionData E W := ⟨6,![cycle2880_0,cycle2880_1,cycle2880_2,cycle2880_3,cycle2880_4,cycle2880_5]⟩
lemma valid_data2880 : data2880.Valid src2880 dst2880 Finset.univ := by decide +kernel

def src2881 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst2881 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle2881_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2881_1 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2881_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2881_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2881_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2881_5 : CycleData E W := ⟨2,![12,18,22,13],![14,27,38,28]⟩
def data2881 : PartitionData E W := ⟨6,![cycle2881_0,cycle2881_1,cycle2881_2,cycle2881_3,cycle2881_4,cycle2881_5]⟩
lemma valid_data2881 : data2881.Valid src2881 dst2881 Finset.univ := by decide +kernel

def src2882 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst2882 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle2882_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2882_1 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2882_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2882_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2882_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2882_5 : CycleData E W := ⟨3,![12,18,22,21,13],![14,27,38,18,28]⟩
def data2882 : PartitionData E W := ⟨6,![cycle2882_0,cycle2882_1,cycle2882_2,cycle2882_3,cycle2882_4,cycle2882_5]⟩
lemma valid_data2882 : data2882.Valid src2882 dst2882 Finset.univ := by decide +kernel

def src2883 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst2883 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle2883_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2883_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2883_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2883_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2883_4 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def cycle2883_5 : CycleData E W := ⟨3,![15,12,13,22,19],![6,27,14,28,38]⟩
def data2883 : PartitionData E W := ⟨6,![cycle2883_0,cycle2883_1,cycle2883_2,cycle2883_3,cycle2883_4,cycle2883_5]⟩
lemma valid_data2883 : data2883.Valid src2883 dst2883 Finset.univ := by decide +kernel

def src2884 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst2884 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle2884_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2884_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,26,38,18]⟩
def cycle2884_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2884_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2884_4 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def cycle2884_5 : CycleData E W := ⟨3,![15,12,13,22,19],![6,27,14,28,38]⟩
def data2884 : PartitionData E W := ⟨6,![cycle2884_0,cycle2884_1,cycle2884_2,cycle2884_3,cycle2884_4,cycle2884_5]⟩
lemma valid_data2884 : data2884.Valid src2884 dst2884 Finset.univ := by decide +kernel

def src2885 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst2885 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle2885_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,27,14]⟩
def cycle2885_1 : CycleData E W := ⟨3,![1,19,18,10,2],![3,6,38,26,4]⟩
def cycle2885_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2885_3 : CycleData E W := ⟨3,![4,23,22,8,9],![2,8,38,18,16]⟩
def cycle2885_4 : CycleData E W := ⟨2,![6,13,21,7],![3,14,28,18]⟩
def cycle2885_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2885 : PartitionData E W := ⟨6,![cycle2885_0,cycle2885_1,cycle2885_2,cycle2885_3,cycle2885_4,cycle2885_5]⟩
lemma valid_data2885 : data2885.Valid src2885 dst2885 Finset.univ := by decide +kernel

def src2886 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst2886 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle2886_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2886_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2886_2 : CycleData E W := ⟨3,![4,23,19,15,9],![2,8,38,6,16]⟩
def cycle2886_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle2886_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2886_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2886 : PartitionData E W := ⟨6,![cycle2886_0,cycle2886_1,cycle2886_2,cycle2886_3,cycle2886_4,cycle2886_5]⟩
lemma valid_data2886 : data2886.Valid src2886 dst2886 Finset.univ := by decide +kernel

def src2887 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst2887 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle2887_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2887_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2887_2 : CycleData E W := ⟨3,![4,23,11,16,9],![2,8,28,26,16]⟩
def cycle2887_3 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2887_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2887_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2887 : PartitionData E W := ⟨6,![cycle2887_0,cycle2887_1,cycle2887_2,cycle2887_3,cycle2887_4,cycle2887_5]⟩
lemma valid_data2887 : data2887.Valid src2887 dst2887 Finset.univ := by decide +kernel

def src2888 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst2888 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle2888_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2888_1 : CycleData E W := ⟨3,![1,19,18,13,6],![3,6,38,27,14]⟩
def cycle2888_2 : CycleData E W := ⟨3,![2,3,23,22,7],![3,4,8,38,18]⟩
def cycle2888_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2888_4 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle2888_5 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def data2888 : PartitionData E W := ⟨6,![cycle2888_0,cycle2888_1,cycle2888_2,cycle2888_3,cycle2888_4,cycle2888_5]⟩
lemma valid_data2888 : data2888.Valid src2888 dst2888 Finset.univ := by decide +kernel

def src2889 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst2889 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle2889_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2889_1 : CycleData E W := ⟨2,![1,19,13,6],![3,6,27,14]⟩
def cycle2889_2 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2889_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2889_4 : CycleData E W := ⟨3,![4,20,21,12,5],![2,8,18,28,14]⟩
def cycle2889_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2889 : PartitionData E W := ⟨6,![cycle2889_0,cycle2889_1,cycle2889_2,cycle2889_3,cycle2889_4,cycle2889_5]⟩
lemma valid_data2889 : data2889.Valid src2889 dst2889 Finset.univ := by decide +kernel

def src2890 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst2890 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle2890_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2890_1 : CycleData E W := ⟨2,![1,19,13,6],![3,6,27,14]⟩
def cycle2890_2 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2890_3 : CycleData E W := ⟨3,![3,20,21,18,14],![4,8,18,38,27]⟩
def cycle2890_4 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle2890_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2890 : PartitionData E W := ⟨6,![cycle2890_0,cycle2890_1,cycle2890_2,cycle2890_3,cycle2890_4,cycle2890_5]⟩
lemma valid_data2890 : data2890.Valid src2890 dst2890 Finset.univ := by decide +kernel

def src2891 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst2891 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle2891_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2891_1 : CycleData E W := ⟨2,![1,19,13,6],![3,6,27,14]⟩
def cycle2891_2 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,26,16,18]⟩
def cycle2891_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2891_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2891_5 : CycleData E W := ⟨2,![21,11,17,22],![18,28,26,38]⟩
def data2891 : PartitionData E W := ⟨6,![cycle2891_0,cycle2891_1,cycle2891_2,cycle2891_3,cycle2891_4,cycle2891_5]⟩
lemma valid_data2891 : data2891.Valid src2891 dst2891 Finset.univ := by decide +kernel

def src2892 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst2892 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle2892_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2892_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2892_2 : CycleData E W := ⟨3,![4,3,14,13,5],![2,8,4,27,14]⟩
def cycle2892_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2892_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle2892_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2892 : PartitionData E W := ⟨6,![cycle2892_0,cycle2892_1,cycle2892_2,cycle2892_3,cycle2892_4,cycle2892_5]⟩
lemma valid_data2892 : data2892.Valid src2892 dst2892 Finset.univ := by decide +kernel

def src2893 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst2893 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle2893_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2893_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2893_2 : CycleData E W := ⟨3,![4,3,14,13,5],![2,8,4,27,14]⟩
def cycle2893_3 : CycleData E W := ⟨3,![6,12,23,20,7],![3,14,28,8,18]⟩
def cycle2893_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle2893_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2893 : PartitionData E W := ⟨6,![cycle2893_0,cycle2893_1,cycle2893_2,cycle2893_3,cycle2893_4,cycle2893_5]⟩
lemma valid_data2893 : data2893.Valid src2893 dst2893 Finset.univ := by decide +kernel

def src2894 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst2894 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle2894_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2894_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2894_2 : CycleData E W := ⟨3,![4,3,14,13,5],![2,8,4,27,14]⟩
def cycle2894_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2894_4 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def cycle2894_5 : CycleData E W := ⟨2,![20,11,18,23],![8,28,26,38]⟩
def data2894 : PartitionData E W := ⟨6,![cycle2894_0,cycle2894_1,cycle2894_2,cycle2894_3,cycle2894_4,cycle2894_5]⟩
lemma valid_data2894 : data2894.Valid src2894 dst2894 Finset.univ := by decide +kernel

def src2895 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst2895 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle2895_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2895_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2895_2 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle2895_3 : CycleData E W := ⟨3,![15,8,21,11,19],![6,16,18,28,26]⟩
def cycle2895_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2895_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2895 : PartitionData E W := ⟨6,![cycle2895_0,cycle2895_1,cycle2895_2,cycle2895_3,cycle2895_4,cycle2895_5]⟩
lemma valid_data2895 : data2895.Valid src2895 dst2895 Finset.univ := by decide +kernel

def src2896 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst2896 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle2896_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2896_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2896_2 : CycleData E W := ⟨4,![4,23,11,19,15,9],![2,8,28,26,6,16]⟩
def cycle2896_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2896_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2896_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2896 : PartitionData E W := ⟨6,![cycle2896_0,cycle2896_1,cycle2896_2,cycle2896_3,cycle2896_4,cycle2896_5]⟩
lemma valid_data2896 : data2896.Valid src2896 dst2896 Finset.univ := by decide +kernel

def src2897 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst2897 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle2897_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2897_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,26,4]⟩
def cycle2897_2 : CycleData E W := ⟨3,![4,3,14,13,5],![2,8,4,27,14]⟩
def cycle2897_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2897_4 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2897_5 : CycleData E W := ⟨3,![20,11,18,17,23],![8,28,26,27,38]⟩
def data2897 : PartitionData E W := ⟨6,![cycle2897_0,cycle2897_1,cycle2897_2,cycle2897_3,cycle2897_4,cycle2897_5]⟩
lemma valid_data2897 : data2897.Valid src2897 dst2897 Finset.univ := by decide +kernel

def src2898 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2898 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2898_0 : CycleData E W := ⟨10,![5,13,18,19,1,2,3,20,21,11,16,9],![2,14,27,38,6,3,4,8,18,28,26,16]⟩
def cycle2898_1 : CycleData E W := ⟨10,![0,15,10,14,17,8,7,6,12,22,23,4],![2,6,26,4,27,16,18,3,14,28,38,8]⟩
def data2898 : PartitionData E W := ⟨2,![cycle2898_0,cycle2898_1]⟩
lemma valid_data2898 : data2898.Valid src2898 dst2898 Finset.univ := by decide +kernel

def src2899 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2899 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2899_0 : CycleData E W := ⟨10,![0,1,2,3,20,21,18,13,12,11,16,9],![2,6,3,4,8,18,38,27,14,28,26,16]⟩
def cycle2899_1 : CycleData E W := ⟨10,![4,23,22,19,15,10,14,17,8,7,6,5],![2,8,28,38,6,26,4,27,16,18,3,14]⟩
def data2899 : PartitionData E W := ⟨2,![cycle2899_0,cycle2899_1]⟩
lemma valid_data2899 : data2899.Valid src2899 dst2899 Finset.univ := by decide +kernel

def src2900 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2900 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2900_0 : CycleData E W := ⟨10,![4,20,21,8,16,10,2,1,19,18,13,5],![2,8,28,18,16,26,4,3,6,38,27,14]⟩
def cycle2900_1 : CycleData E W := ⟨10,![0,15,11,12,6,7,22,23,3,14,17,9],![2,6,26,28,14,3,18,38,8,4,27,16]⟩
def data2900 : PartitionData E W := ⟨2,![cycle2900_0,cycle2900_1]⟩
lemma valid_data2900 : data2900.Valid src2900 dst2900 Finset.univ := by decide +kernel

def src2901 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2901 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2901_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2901_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2901_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2901_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle2901_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2901_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2901 : PartitionData E W := ⟨6,![cycle2901_0,cycle2901_1,cycle2901_2,cycle2901_3,cycle2901_4,cycle2901_5]⟩
lemma valid_data2901 : data2901.Valid src2901 dst2901 Finset.univ := by decide +kernel

def src2902 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2902 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2902_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2902_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2902_2 : CycleData E W := ⟨3,![4,23,11,16,9],![2,8,28,26,16]⟩
def cycle2902_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2902_4 : CycleData E W := ⟨2,![10,15,19,14],![4,26,6,27]⟩
def cycle2902_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2902 : PartitionData E W := ⟨6,![cycle2902_0,cycle2902_1,cycle2902_2,cycle2902_3,cycle2902_4,cycle2902_5]⟩
lemma valid_data2902 : data2902.Valid src2902 dst2902 Finset.univ := by decide +kernel

def src2903 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2903 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2903_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle2903_1 : CycleData E W := ⟨2,![1,19,13,6],![3,6,27,14]⟩
def cycle2903_2 : CycleData E W := ⟨3,![2,10,11,21,7],![3,4,26,28,18]⟩
def cycle2903_3 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2903_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2903_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2903 : PartitionData E W := ⟨6,![cycle2903_0,cycle2903_1,cycle2903_2,cycle2903_3,cycle2903_4,cycle2903_5]⟩
lemma valid_data2903 : data2903.Valid src2903 dst2903 Finset.univ := by decide +kernel

def src2904 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2904 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2904_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle2904_1 : CycleData E W := ⟨3,![1,19,23,3,2],![3,6,38,8,4]⟩
def cycle2904_2 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2904_3 : CycleData E W := ⟨2,![6,12,21,7],![3,14,28,18]⟩
def cycle2904_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2904_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2904 : PartitionData E W := ⟨6,![cycle2904_0,cycle2904_1,cycle2904_2,cycle2904_3,cycle2904_4,cycle2904_5]⟩
lemma valid_data2904 : data2904.Valid src2904 dst2904 Finset.univ := by decide +kernel

def src2905 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2905 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2905_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle2905_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2905_2 : CycleData E W := ⟨3,![2,3,23,12,6],![3,4,8,28,14]⟩
def cycle2905_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2905_4 : CycleData E W := ⟨2,![10,17,16,14],![4,26,16,27]⟩
def cycle2905_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2905 : PartitionData E W := ⟨6,![cycle2905_0,cycle2905_1,cycle2905_2,cycle2905_3,cycle2905_4,cycle2905_5]⟩
lemma valid_data2905 : data2905.Valid src2905 dst2905 Finset.univ := by decide +kernel

def src2906 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2906 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2906_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle2906_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2906_2 : CycleData E W := ⟨2,![2,14,13,6],![3,4,27,14]⟩
def cycle2906_3 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2906_4 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2906_5 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def data2906 : PartitionData E W := ⟨6,![cycle2906_0,cycle2906_1,cycle2906_2,cycle2906_3,cycle2906_4,cycle2906_5]⟩
lemma valid_data2906 : data2906.Valid src2906 dst2906 Finset.univ := by decide +kernel

def src2907 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst2907 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle2907_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2907_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2907_2 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2907_3 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def cycle2907_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2907_5 : CycleData E W := ⟨3,![15,13,12,22,19],![6,27,14,28,38]⟩
def data2907 : PartitionData E W := ⟨6,![cycle2907_0,cycle2907_1,cycle2907_2,cycle2907_3,cycle2907_4,cycle2907_5]⟩
lemma valid_data2907 : data2907.Valid src2907 dst2907 Finset.univ := by decide +kernel

def src2908 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst2908 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle2908_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2908_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2908_2 : CycleData E W := ⟨3,![4,23,11,17,9],![2,8,28,26,16]⟩
def cycle2908_3 : CycleData E W := ⟨1,![8,21,18],![16,18,38]⟩
def cycle2908_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2908_5 : CycleData E W := ⟨3,![15,13,12,22,19],![6,27,14,28,38]⟩
def data2908 : PartitionData E W := ⟨6,![cycle2908_0,cycle2908_1,cycle2908_2,cycle2908_3,cycle2908_4,cycle2908_5]⟩
lemma valid_data2908 : data2908.Valid src2908 dst2908 Finset.univ := by decide +kernel

def src2909 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst2909 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle2909_0 : CycleData E W := ⟨2,![0,15,13,5],![2,6,27,14]⟩
def cycle2909_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2909_2 : CycleData E W := ⟨3,![2,3,20,12,6],![3,4,8,28,14]⟩
def cycle2909_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2909_4 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def cycle2909_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data2909 : PartitionData E W := ⟨6,![cycle2909_0,cycle2909_1,cycle2909_2,cycle2909_3,cycle2909_4,cycle2909_5]⟩
lemma valid_data2909 : data2909.Valid src2909 dst2909 Finset.univ := by decide +kernel

def src2910 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst2910 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle2910_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2910_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2910_2 : CycleData E W := ⟨3,![4,23,19,15,9],![2,8,38,6,16]⟩
def cycle2910_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2910_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2910_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2910 : PartitionData E W := ⟨6,![cycle2910_0,cycle2910_1,cycle2910_2,cycle2910_3,cycle2910_4,cycle2910_5]⟩
lemma valid_data2910 : data2910.Valid src2910 dst2910 Finset.univ := by decide +kernel

def src2911 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst2911 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle2911_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2911_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2911_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle2911_3 : CycleData E W := ⟨2,![15,8,21,19],![6,16,18,38]⟩
def cycle2911_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2911_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2911 : PartitionData E W := ⟨6,![cycle2911_0,cycle2911_1,cycle2911_2,cycle2911_3,cycle2911_4,cycle2911_5]⟩
lemma valid_data2911 : data2911.Valid src2911 dst2911 Finset.univ := by decide +kernel

def src2912 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst2912 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle2912_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2912_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2912_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2912_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle2912_4 : CycleData E W := ⟨2,![15,8,22,19],![6,16,18,38]⟩
def cycle2912_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2912 : PartitionData E W := ⟨6,![cycle2912_0,cycle2912_1,cycle2912_2,cycle2912_3,cycle2912_4,cycle2912_5]⟩
lemma valid_data2912 : data2912.Valid src2912 dst2912 Finset.univ := by decide +kernel

def src2913 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst2913 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle2913_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2913_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2913_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2913_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2913_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,26,14,27]⟩
def cycle2913_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2913 : PartitionData E W := ⟨6,![cycle2913_0,cycle2913_1,cycle2913_2,cycle2913_3,cycle2913_4,cycle2913_5]⟩
lemma valid_data2913 : data2913.Valid src2913 dst2913 Finset.univ := by decide +kernel

def src2914 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst2914 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle2914_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2914_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,27,38,18]⟩
def cycle2914_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2914_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2914_4 : CycleData E W := ⟨3,![15,16,12,11,19],![6,16,26,14,27]⟩
def cycle2914_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2914 : PartitionData E W := ⟨6,![cycle2914_0,cycle2914_1,cycle2914_2,cycle2914_3,cycle2914_4,cycle2914_5]⟩
lemma valid_data2914 : data2914.Valid src2914 dst2914 Finset.univ := by decide +kernel

def src2915 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst2915 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle2915_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2915_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,27,4]⟩
def cycle2915_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2915_3 : CycleData E W := ⟨3,![4,23,17,12,5],![2,8,38,26,14]⟩
def cycle2915_4 : CycleData E W := ⟨3,![6,11,18,22,7],![3,14,27,38,18]⟩
def cycle2915_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2915 : PartitionData E W := ⟨6,![cycle2915_0,cycle2915_1,cycle2915_2,cycle2915_3,cycle2915_4,cycle2915_5]⟩
lemma valid_data2915 : data2915.Valid src2915 dst2915 Finset.univ := by decide +kernel

def src2916 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst2916 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle2916_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2916_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2916_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,27]⟩
def cycle2916_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2916_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,27,14,26]⟩
def cycle2916_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2916 : PartitionData E W := ⟨6,![cycle2916_0,cycle2916_1,cycle2916_2,cycle2916_3,cycle2916_4,cycle2916_5]⟩
lemma valid_data2916 : data2916.Valid src2916 dst2916 Finset.univ := by decide +kernel

def src2917 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst2917 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle2917_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2917_1 : CycleData E W := ⟨3,![2,10,17,21,7],![3,4,27,38,18]⟩
def cycle2917_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2917_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2917_4 : CycleData E W := ⟨3,![15,16,11,12,19],![6,16,27,14,26]⟩
def cycle2917_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2917 : PartitionData E W := ⟨6,![cycle2917_0,cycle2917_1,cycle2917_2,cycle2917_3,cycle2917_4,cycle2917_5]⟩
lemma valid_data2917 : data2917.Valid src2917 dst2917 Finset.univ := by decide +kernel

def src2918 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst2918 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle2918_0 : CycleData E W := ⟨1,![0,15,9],![2,6,16]⟩
def cycle2918_1 : CycleData E W := ⟨2,![1,19,12,6],![3,6,26,14]⟩
def cycle2918_2 : CycleData E W := ⟨3,![2,10,16,8,7],![3,4,27,16,18]⟩
def cycle2918_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2918_4 : CycleData E W := ⟨3,![4,23,17,11,5],![2,8,38,27,14]⟩
def cycle2918_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data2918 : PartitionData E W := ⟨6,![cycle2918_0,cycle2918_1,cycle2918_2,cycle2918_3,cycle2918_4,cycle2918_5]⟩
lemma valid_data2918 : data2918.Valid src2918 dst2918 Finset.univ := by decide +kernel

def src2919 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst2919 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle2919_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2919_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2919_2 : CycleData E W := ⟨2,![4,23,16,9],![2,8,38,16]⟩
def cycle2919_3 : CycleData E W := ⟨3,![15,8,21,13,19],![6,16,18,28,26]⟩
def cycle2919_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle2919_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2919 : PartitionData E W := ⟨6,![cycle2919_0,cycle2919_1,cycle2919_2,cycle2919_3,cycle2919_4,cycle2919_5]⟩
lemma valid_data2919 : data2919.Valid src2919 dst2919 Finset.univ := by decide +kernel

def src2920 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst2920 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle2920_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2920_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2920_2 : CycleData E W := ⟨4,![4,23,13,19,15,9],![2,8,28,26,6,16]⟩
def cycle2920_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2920_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle2920_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2920 : PartitionData E W := ⟨6,![cycle2920_0,cycle2920_1,cycle2920_2,cycle2920_3,cycle2920_4,cycle2920_5]⟩
lemma valid_data2920 : data2920.Valid src2920 dst2920 Finset.univ := by decide +kernel

def src2921 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst2921 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle2921_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2921_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2921_2 : CycleData E W := ⟨2,![3,23,17,10],![4,8,38,27]⟩
def cycle2921_3 : CycleData E W := ⟨4,![4,20,13,19,15,9],![2,8,28,26,6,16]⟩
def cycle2921_4 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2921_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2921 : PartitionData E W := ⟨6,![cycle2921_0,cycle2921_1,cycle2921_2,cycle2921_3,cycle2921_4,cycle2921_5]⟩
lemma valid_data2921 : data2921.Valid src2921 dst2921 Finset.univ := by decide +kernel

def src2922 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2922 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2922_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2922_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2922_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2922_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2922_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle2922_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2922 : PartitionData E W := ⟨6,![cycle2922_0,cycle2922_1,cycle2922_2,cycle2922_3,cycle2922_4,cycle2922_5]⟩
lemma valid_data2922 : data2922.Valid src2922 dst2922 Finset.univ := by decide +kernel

def src2923 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2923 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2923_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2923_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,27,38,18]⟩
def cycle2923_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2923_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2923_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle2923_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2923 : PartitionData E W := ⟨6,![cycle2923_0,cycle2923_1,cycle2923_2,cycle2923_3,cycle2923_4,cycle2923_5]⟩
lemma valid_data2923 : data2923.Valid src2923 dst2923 Finset.univ := by decide +kernel

def src2924 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2924 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2924_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle2924_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2924_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,27,14]⟩
def cycle2924_3 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2924_4 : CycleData E W := ⟨3,![4,23,18,17,9],![2,8,38,27,16]⟩
def cycle2924_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2924 : PartitionData E W := ⟨6,![cycle2924_0,cycle2924_1,cycle2924_2,cycle2924_3,cycle2924_4,cycle2924_5]⟩
lemma valid_data2924 : data2924.Valid src2924 dst2924 Finset.univ := by decide +kernel

def src2925 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2925 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2925_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2925_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2925_2 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2925_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2925_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2925_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2925 : PartitionData E W := ⟨6,![cycle2925_0,cycle2925_1,cycle2925_2,cycle2925_3,cycle2925_4,cycle2925_5]⟩
lemma valid_data2925 : data2925.Valid src2925 dst2925 Finset.univ := by decide +kernel

def src2926 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2926 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2926_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2926_1 : CycleData E W := ⟨2,![2,3,20,7],![3,4,8,18]⟩
def cycle2926_2 : CycleData E W := ⟨3,![4,23,13,16,9],![2,8,28,26,16]⟩
def cycle2926_3 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2926_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2926_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2926 : PartitionData E W := ⟨6,![cycle2926_0,cycle2926_1,cycle2926_2,cycle2926_3,cycle2926_4,cycle2926_5]⟩
lemma valid_data2926 : data2926.Valid src2926 dst2926 Finset.univ := by decide +kernel

def src2927 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2927 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2927_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2927_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2927_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2927_3 : CycleData E W := ⟨3,![4,20,13,16,9],![2,8,28,26,16]⟩
def cycle2927_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2927_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2927 : PartitionData E W := ⟨6,![cycle2927_0,cycle2927_1,cycle2927_2,cycle2927_3,cycle2927_4,cycle2927_5]⟩
lemma valid_data2927 : data2927.Valid src2927 dst2927 Finset.univ := by decide +kernel

def src2928 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst2928 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle2928_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2928_1 : CycleData E W := ⟨3,![2,10,17,8,7],![3,4,27,16,18]⟩
def cycle2928_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2928_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2928_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2928_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2928 : PartitionData E W := ⟨6,![cycle2928_0,cycle2928_1,cycle2928_2,cycle2928_3,cycle2928_4,cycle2928_5]⟩
lemma valid_data2928 : data2928.Valid src2928 dst2928 Finset.univ := by decide +kernel

def src2929 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst2929 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle2929_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2929_1 : CycleData E W := ⟨3,![2,10,17,8,7],![3,4,27,16,18]⟩
def cycle2929_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2929_3 : CycleData E W := ⟨3,![4,20,21,18,9],![2,8,18,38,16]⟩
def cycle2929_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2929_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2929 : PartitionData E W := ⟨6,![cycle2929_0,cycle2929_1,cycle2929_2,cycle2929_3,cycle2929_4,cycle2929_5]⟩
lemma valid_data2929 : data2929.Valid src2929 dst2929 Finset.univ := by decide +kernel

def src2930 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst2930 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle2930_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2930_1 : CycleData E W := ⟨3,![2,10,17,8,7],![3,4,27,16,18]⟩
def cycle2930_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2930_3 : CycleData E W := ⟨2,![4,23,18,9],![2,8,38,16]⟩
def cycle2930_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2930_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2930 : PartitionData E W := ⟨6,![cycle2930_0,cycle2930_1,cycle2930_2,cycle2930_3,cycle2930_4,cycle2930_5]⟩
lemma valid_data2930 : data2930.Valid src2930 dst2930 Finset.univ := by decide +kernel

def src2931 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2931 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2931_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2931_1 : CycleData E W := ⟨3,![2,10,18,8,7],![3,4,27,16,18]⟩
def cycle2931_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2931_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2931_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2931_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2931 : PartitionData E W := ⟨6,![cycle2931_0,cycle2931_1,cycle2931_2,cycle2931_3,cycle2931_4,cycle2931_5]⟩
lemma valid_data2931 : data2931.Valid src2931 dst2931 Finset.univ := by decide +kernel

def src2932 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2932 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2932_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2932_1 : CycleData E W := ⟨3,![2,10,18,8,7],![3,4,27,16,18]⟩
def cycle2932_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2932_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2932_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2932_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2932 : PartitionData E W := ⟨6,![cycle2932_0,cycle2932_1,cycle2932_2,cycle2932_3,cycle2932_4,cycle2932_5]⟩
lemma valid_data2932 : data2932.Valid src2932 dst2932 Finset.univ := by decide +kernel

def src2933 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2933 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2933_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2933_1 : CycleData E W := ⟨3,![2,10,18,8,7],![3,4,27,16,18]⟩
def cycle2933_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2933_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2933_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2933_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2933 : PartitionData E W := ⟨6,![cycle2933_0,cycle2933_1,cycle2933_2,cycle2933_3,cycle2933_4,cycle2933_5]⟩
lemma valid_data2933 : data2933.Valid src2933 dst2933 Finset.univ := by decide +kernel

def src2934 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst2934 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle2934_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2934_1 : CycleData E W := ⟨2,![2,14,21,7],![3,4,28,18]⟩
def cycle2934_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2934_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2934_4 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def cycle2934_5 : CycleData E W := ⟨3,![15,12,13,22,19],![6,26,14,28,38]⟩
def data2934 : PartitionData E W := ⟨6,![cycle2934_0,cycle2934_1,cycle2934_2,cycle2934_3,cycle2934_4,cycle2934_5]⟩
lemma valid_data2934 : data2934.Valid src2934 dst2934 Finset.univ := by decide +kernel

def src2935 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst2935 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle2935_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2935_1 : CycleData E W := ⟨3,![2,10,18,21,7],![3,4,27,38,18]⟩
def cycle2935_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2935_3 : CycleData E W := ⟨2,![4,20,8,9],![2,8,18,16]⟩
def cycle2935_4 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def cycle2935_5 : CycleData E W := ⟨3,![15,12,13,22,19],![6,26,14,28,38]⟩
def data2935 : PartitionData E W := ⟨6,![cycle2935_0,cycle2935_1,cycle2935_2,cycle2935_3,cycle2935_4,cycle2935_5]⟩
lemma valid_data2935 : data2935.Valid src2935 dst2935 Finset.univ := by decide +kernel

def src2936 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst2936 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle2936_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle2936_1 : CycleData E W := ⟨3,![1,19,18,10,2],![3,6,38,27,4]⟩
def cycle2936_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2936_3 : CycleData E W := ⟨3,![4,23,22,8,9],![2,8,38,18,16]⟩
def cycle2936_4 : CycleData E W := ⟨2,![6,13,21,7],![3,14,28,18]⟩
def cycle2936_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2936 : PartitionData E W := ⟨6,![cycle2936_0,cycle2936_1,cycle2936_2,cycle2936_3,cycle2936_4,cycle2936_5]⟩
lemma valid_data2936 : data2936.Valid src2936 dst2936 Finset.univ := by decide +kernel

def src2937 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst2937 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle2937_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2937_1 : CycleData E W := ⟨3,![2,10,18,8,7],![3,4,27,16,18]⟩
def cycle2937_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2937_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2937_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2937_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2937 : PartitionData E W := ⟨6,![cycle2937_0,cycle2937_1,cycle2937_2,cycle2937_3,cycle2937_4,cycle2937_5]⟩
lemma valid_data2937 : data2937.Valid src2937 dst2937 Finset.univ := by decide +kernel

def src2938 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst2938 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle2938_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2938_1 : CycleData E W := ⟨3,![2,10,18,8,7],![3,4,27,16,18]⟩
def cycle2938_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2938_3 : CycleData E W := ⟨3,![4,20,21,17,9],![2,8,18,38,16]⟩
def cycle2938_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2938_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2938 : PartitionData E W := ⟨6,![cycle2938_0,cycle2938_1,cycle2938_2,cycle2938_3,cycle2938_4,cycle2938_5]⟩
lemma valid_data2938 : data2938.Valid src2938 dst2938 Finset.univ := by decide +kernel

def src2939 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst2939 : E → W := ![6,3,4,8,2,14,3,18,16,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle2939_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle2939_1 : CycleData E W := ⟨3,![2,10,18,8,7],![3,4,27,16,18]⟩
def cycle2939_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2939_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2939_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2939_5 : CycleData E W := ⟨3,![12,16,22,21,13],![14,26,38,18,28]⟩
def data2939 : PartitionData E W := ⟨6,![cycle2939_0,cycle2939_1,cycle2939_2,cycle2939_3,cycle2939_4,cycle2939_5]⟩
lemma valid_data2939 : data2939.Valid src2939 dst2939 Finset.univ := by decide +kernel

def src2940 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2940 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2940_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2940_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle2940_2 : CycleData E W := ⟨3,![3,23,17,16,10],![4,8,38,16,26]⟩
def cycle2940_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2940_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2940_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2940 : PartitionData E W := ⟨6,![cycle2940_0,cycle2940_1,cycle2940_2,cycle2940_3,cycle2940_4,cycle2940_5]⟩
lemma valid_data2940 : data2940.Valid src2940 dst2940 Finset.univ := by decide +kernel

def src2941 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2941 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2941_0 : CycleData E W := ⟨2,![0,19,12,5],![2,6,27,14]⟩
def cycle2941_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle2941_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2941_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2941_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2941_5 : CycleData E W := ⟨2,![7,17,21,8],![3,16,38,18]⟩
def cycle2941_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2941 : PartitionData E W := ⟨7,![cycle2941_0,cycle2941_1,cycle2941_2,cycle2941_3,cycle2941_4,cycle2941_5,cycle2941_6]⟩
lemma valid_data2941 : data2941.Valid src2941 dst2941 Finset.univ := by decide +kernel

def src2942 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2942 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2942_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2942_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2942_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2942_3 : CycleData E W := ⟨3,![4,23,17,6,5],![2,8,38,16,14]⟩
def cycle2942_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2942_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2942 : PartitionData E W := ⟨6,![cycle2942_0,cycle2942_1,cycle2942_2,cycle2942_3,cycle2942_4,cycle2942_5]⟩
lemma valid_data2942 : data2942.Valid src2942 dst2942 Finset.univ := by decide +kernel

def src2943 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2943 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2943_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2943_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle2943_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2943_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2943_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2943_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2943 : PartitionData E W := ⟨6,![cycle2943_0,cycle2943_1,cycle2943_2,cycle2943_3,cycle2943_4,cycle2943_5]⟩
lemma valid_data2943 : data2943.Valid src2943 dst2943 Finset.univ := by decide +kernel

def src2944 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2944 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2944_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2944_1 : CycleData E W := ⟨3,![2,10,16,21,8],![3,4,26,38,18]⟩
def cycle2944_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2944_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2944_4 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def cycle2944_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2944 : PartitionData E W := ⟨6,![cycle2944_0,cycle2944_1,cycle2944_2,cycle2944_3,cycle2944_4,cycle2944_5]⟩
lemma valid_data2944 : data2944.Valid src2944 dst2944 Finset.univ := by decide +kernel

def src2945 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2945 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2945_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2945_1 : CycleData E W := ⟨3,![1,19,13,14,2],![3,6,27,28,4]⟩
def cycle2945_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2945_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2945_4 : CycleData E W := ⟨1,![6,18,12],![14,16,27]⟩
def cycle2945_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data2945 : PartitionData E W := ⟨6,![cycle2945_0,cycle2945_1,cycle2945_2,cycle2945_3,cycle2945_4,cycle2945_5]⟩
lemma valid_data2945 : data2945.Valid src2945 dst2945 Finset.univ := by decide +kernel

def src2946 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2946 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2946_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2946_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle2946_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2946_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2946_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle2946_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2946 : PartitionData E W := ⟨6,![cycle2946_0,cycle2946_1,cycle2946_2,cycle2946_3,cycle2946_4,cycle2946_5]⟩
lemma valid_data2946 : data2946.Valid src2946 dst2946 Finset.univ := by decide +kernel

def src2947 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2947 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2947_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2947_1 : CycleData E W := ⟨3,![2,10,18,21,8],![3,4,26,38,18]⟩
def cycle2947_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2947_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2947_4 : CycleData E W := ⟨2,![11,17,16,12],![14,26,16,27]⟩
def cycle2947_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2947 : PartitionData E W := ⟨6,![cycle2947_0,cycle2947_1,cycle2947_2,cycle2947_3,cycle2947_4,cycle2947_5]⟩
lemma valid_data2947 : data2947.Valid src2947 dst2947 Finset.univ := by decide +kernel

def src2948 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2948 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2948_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2948_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2948_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2948_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle2948_4 : CycleData E W := ⟨1,![6,16,12],![14,16,27]⟩
def cycle2948_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2948 : PartitionData E W := ⟨6,![cycle2948_0,cycle2948_1,cycle2948_2,cycle2948_3,cycle2948_4,cycle2948_5]⟩
lemma valid_data2948 : data2948.Valid src2948 dst2948 Finset.univ := by decide +kernel

def src2949 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2949 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2949_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2949_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2949_2 : CycleData E W := ⟨3,![3,23,19,15,10],![4,8,38,6,26]⟩
def cycle2949_3 : CycleData E W := ⟨3,![4,20,21,12,5],![2,8,18,28,14]⟩
def cycle2949_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2949_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2949 : PartitionData E W := ⟨6,![cycle2949_0,cycle2949_1,cycle2949_2,cycle2949_3,cycle2949_4,cycle2949_5]⟩
lemma valid_data2949 : data2949.Valid src2949 dst2949 Finset.univ := by decide +kernel

def src2950 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2950 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2950_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2950_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2950_2 : CycleData E W := ⟨4,![3,20,21,19,15,10],![4,8,18,38,6,26]⟩
def cycle2950_3 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle2950_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2950_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2950 : PartitionData E W := ⟨6,![cycle2950_0,cycle2950_1,cycle2950_2,cycle2950_3,cycle2950_4,cycle2950_5]⟩
lemma valid_data2950 : data2950.Valid src2950 dst2950 Finset.univ := by decide +kernel

def src2951 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2951 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2951_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2951_1 : CycleData E W := ⟨2,![2,14,17,7],![3,4,27,16]⟩
def cycle2951_2 : CycleData E W := ⟨3,![3,23,19,15,10],![4,8,38,6,26]⟩
def cycle2951_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2951_4 : CycleData E W := ⟨1,![6,16,11],![14,16,26]⟩
def cycle2951_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2951 : PartitionData E W := ⟨6,![cycle2951_0,cycle2951_1,cycle2951_2,cycle2951_3,cycle2951_4,cycle2951_5]⟩
lemma valid_data2951 : data2951.Valid src2951 dst2951 Finset.univ := by decide +kernel

def src2952 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2952 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2952_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2952_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2952_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2952_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2952_4 : CycleData E W := ⟨2,![6,18,13,12],![14,16,27,28]⟩
def cycle2952_5 : CycleData E W := ⟨3,![7,17,22,21,8],![3,16,38,28,18]⟩
def data2952 : PartitionData E W := ⟨6,![cycle2952_0,cycle2952_1,cycle2952_2,cycle2952_3,cycle2952_4,cycle2952_5]⟩
lemma valid_data2952 : data2952.Valid src2952 dst2952 Finset.univ := by decide +kernel

def src2953 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2953 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2953_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2953_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2953_2 : CycleData E W := ⟨3,![3,23,22,16,10],![4,8,28,38,26]⟩
def cycle2953_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2953_4 : CycleData E W := ⟨2,![6,18,13,12],![14,16,27,28]⟩
def cycle2953_5 : CycleData E W := ⟨2,![7,17,21,8],![3,16,38,18]⟩
def data2953 : PartitionData E W := ⟨6,![cycle2953_0,cycle2953_1,cycle2953_2,cycle2953_3,cycle2953_4,cycle2953_5]⟩
lemma valid_data2953 : data2953.Valid src2953 dst2953 Finset.univ := by decide +kernel

def src2954 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2954 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2954_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2954_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2954_2 : CycleData E W := ⟨2,![3,23,16,10],![4,8,38,26]⟩
def cycle2954_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2954_4 : CycleData E W := ⟨2,![6,18,13,12],![14,16,27,28]⟩
def cycle2954_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data2954 : PartitionData E W := ⟨6,![cycle2954_0,cycle2954_1,cycle2954_2,cycle2954_3,cycle2954_4,cycle2954_5]⟩
lemma valid_data2954 : data2954.Valid src2954 dst2954 Finset.univ := by decide +kernel

def src2955 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2955 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2955_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2955_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2955_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2955_3 : CycleData E W := ⟨3,![4,20,21,12,5],![2,8,18,28,14]⟩
def cycle2955_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle2955_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2955 : PartitionData E W := ⟨6,![cycle2955_0,cycle2955_1,cycle2955_2,cycle2955_3,cycle2955_4,cycle2955_5]⟩
lemma valid_data2955 : data2955.Valid src2955 dst2955 Finset.univ := by decide +kernel

def src2956 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2956 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2956_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2956_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2956_2 : CycleData E W := ⟨3,![3,20,21,18,10],![4,8,18,38,26]⟩
def cycle2956_3 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle2956_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle2956_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2956 : PartitionData E W := ⟨6,![cycle2956_0,cycle2956_1,cycle2956_2,cycle2956_3,cycle2956_4,cycle2956_5]⟩
lemma valid_data2956 : data2956.Valid src2956 dst2956 Finset.univ := by decide +kernel

def src2957 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2957 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2957_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2957_1 : CycleData E W := ⟨2,![2,14,16,7],![3,4,27,16]⟩
def cycle2957_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,26]⟩
def cycle2957_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2957_4 : CycleData E W := ⟨1,![6,17,11],![14,16,26]⟩
def cycle2957_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2957 : PartitionData E W := ⟨6,![cycle2957_0,cycle2957_1,cycle2957_2,cycle2957_3,cycle2957_4,cycle2957_5]⟩
lemma valid_data2957 : data2957.Valid src2957 dst2957 Finset.univ := by decide +kernel

def src2958 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2958 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2958_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2958_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2958_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2958_3 : CycleData E W := ⟨3,![4,20,21,12,5],![2,8,18,28,14]⟩
def cycle2958_4 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle2958_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2958 : PartitionData E W := ⟨6,![cycle2958_0,cycle2958_1,cycle2958_2,cycle2958_3,cycle2958_4,cycle2958_5]⟩
lemma valid_data2958 : data2958.Valid src2958 dst2958 Finset.univ := by decide +kernel

def src2959 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2959 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2959_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2959_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2959_2 : CycleData E W := ⟨3,![3,20,21,18,14],![4,8,18,38,27]⟩
def cycle2959_3 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle2959_4 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle2959_5 : CycleData E W := ⟨2,![15,11,22,19],![6,26,28,38]⟩
def data2959 : PartitionData E W := ⟨6,![cycle2959_0,cycle2959_1,cycle2959_2,cycle2959_3,cycle2959_4,cycle2959_5]⟩
lemma valid_data2959 : data2959.Valid src2959 dst2959 Finset.univ := by decide +kernel

def src2960 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2960 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2960_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2960_1 : CycleData E W := ⟨2,![2,10,16,7],![3,4,26,16]⟩
def cycle2960_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2960_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2960_4 : CycleData E W := ⟨1,![6,17,13],![14,16,27]⟩
def cycle2960_5 : CycleData E W := ⟨3,![15,11,21,22,19],![6,26,28,18,38]⟩
def data2960 : PartitionData E W := ⟨6,![cycle2960_0,cycle2960_1,cycle2960_2,cycle2960_3,cycle2960_4,cycle2960_5]⟩
lemma valid_data2960 : data2960.Valid src2960 dst2960 Finset.univ := by decide +kernel

def src2961 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2961 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2961_0 : CycleData E W := ⟨2,![0,19,13,5],![2,6,27,14]⟩
def cycle2961_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle2961_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2961_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2961_4 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def cycle2961_5 : CycleData E W := ⟨3,![7,17,22,21,8],![3,16,38,28,18]⟩
def data2961 : PartitionData E W := ⟨6,![cycle2961_0,cycle2961_1,cycle2961_2,cycle2961_3,cycle2961_4,cycle2961_5]⟩
lemma valid_data2961 : data2961.Valid src2961 dst2961 Finset.univ := by decide +kernel

def src2962 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2962 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2962_0 : CycleData E W := ⟨3,![0,15,16,6,5],![2,6,26,16,14]⟩
def cycle2962_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2962_2 : CycleData E W := ⟨2,![3,23,11,10],![4,8,28,26]⟩
def cycle2962_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2962_4 : CycleData E W := ⟨2,![7,17,21,8],![3,16,38,18]⟩
def cycle2962_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2962 : PartitionData E W := ⟨6,![cycle2962_0,cycle2962_1,cycle2962_2,cycle2962_3,cycle2962_4,cycle2962_5]⟩
lemma valid_data2962 : data2962.Valid src2962 dst2962 Finset.univ := by decide +kernel

def src2963 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2963 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2963_0 : CycleData E W := ⟨2,![0,19,13,5],![2,6,27,14]⟩
def cycle2963_1 : CycleData E W := ⟨2,![1,15,10,2],![3,6,26,4]⟩
def cycle2963_2 : CycleData E W := ⟨2,![3,23,18,14],![4,8,38,27]⟩
def cycle2963_3 : CycleData E W := ⟨2,![4,20,21,9],![2,8,28,18]⟩
def cycle2963_4 : CycleData E W := ⟨2,![6,16,11,12],![14,16,26,28]⟩
def cycle2963_5 : CycleData E W := ⟨2,![7,17,22,8],![3,16,38,18]⟩
def data2963 : PartitionData E W := ⟨6,![cycle2963_0,cycle2963_1,cycle2963_2,cycle2963_3,cycle2963_4,cycle2963_5]⟩
lemma valid_data2963 : data2963.Valid src2963 dst2963 Finset.univ := by decide +kernel

def src2964 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2964 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2964_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2964_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2964_2 : CycleData E W := ⟨3,![3,23,19,15,14],![4,8,38,6,27]⟩
def cycle2964_3 : CycleData E W := ⟨3,![4,20,21,12,5],![2,8,18,28,14]⟩
def cycle2964_4 : CycleData E W := ⟨1,![6,16,13],![14,16,27]⟩
def cycle2964_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2964 : PartitionData E W := ⟨6,![cycle2964_0,cycle2964_1,cycle2964_2,cycle2964_3,cycle2964_4,cycle2964_5]⟩
lemma valid_data2964 : data2964.Valid src2964 dst2964 Finset.univ := by decide +kernel

def src2965 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2965 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2965_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2965_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2965_2 : CycleData E W := ⟨4,![3,20,21,19,15,14],![4,8,18,38,6,27]⟩
def cycle2965_3 : CycleData E W := ⟨2,![4,23,12,5],![2,8,28,14]⟩
def cycle2965_4 : CycleData E W := ⟨1,![6,16,13],![14,16,27]⟩
def cycle2965_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2965 : PartitionData E W := ⟨6,![cycle2965_0,cycle2965_1,cycle2965_2,cycle2965_3,cycle2965_4,cycle2965_5]⟩
lemma valid_data2965 : data2965.Valid src2965 dst2965 Finset.univ := by decide +kernel

def src2966 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2966 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2966_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2966_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,26,16]⟩
def cycle2966_2 : CycleData E W := ⟨3,![3,23,19,15,14],![4,8,38,6,27]⟩
def cycle2966_3 : CycleData E W := ⟨2,![4,20,12,5],![2,8,28,14]⟩
def cycle2966_4 : CycleData E W := ⟨1,![6,16,13],![14,16,27]⟩
def cycle2966_5 : CycleData E W := ⟨2,![21,11,18,22],![18,28,26,38]⟩
def data2966 : PartitionData E W := ⟨6,![cycle2966_0,cycle2966_1,cycle2966_2,cycle2966_3,cycle2966_4,cycle2966_5]⟩
lemma valid_data2966 : data2966.Valid src2966 dst2966 Finset.univ := by decide +kernel

def src2967 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2967 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2967_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2967_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle2967_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2967_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2967_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle2967_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2967 : PartitionData E W := ⟨6,![cycle2967_0,cycle2967_1,cycle2967_2,cycle2967_3,cycle2967_4,cycle2967_5]⟩
lemma valid_data2967 : data2967.Valid src2967 dst2967 Finset.univ := by decide +kernel

def src2968 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2968 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2968_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2968_1 : CycleData E W := ⟨3,![2,10,18,21,8],![3,4,27,38,18]⟩
def cycle2968_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2968_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2968_4 : CycleData E W := ⟨2,![11,17,16,12],![14,27,16,26]⟩
def cycle2968_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2968 : PartitionData E W := ⟨6,![cycle2968_0,cycle2968_1,cycle2968_2,cycle2968_3,cycle2968_4,cycle2968_5]⟩
lemma valid_data2968 : data2968.Valid src2968 dst2968 Finset.univ := by decide +kernel

def src2969 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2969 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2969_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2969_1 : CycleData E W := ⟨2,![2,10,17,7],![3,4,27,16]⟩
def cycle2969_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2969_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle2969_4 : CycleData E W := ⟨1,![6,16,12],![14,16,26]⟩
def cycle2969_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2969 : PartitionData E W := ⟨6,![cycle2969_0,cycle2969_1,cycle2969_2,cycle2969_3,cycle2969_4,cycle2969_5]⟩
lemma valid_data2969 : data2969.Valid src2969 dst2969 Finset.univ := by decide +kernel

def src2970 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2970 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2970_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2970_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle2970_2 : CycleData E W := ⟨2,![3,23,18,10],![4,8,38,27]⟩
def cycle2970_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2970_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2970_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2970 : PartitionData E W := ⟨6,![cycle2970_0,cycle2970_1,cycle2970_2,cycle2970_3,cycle2970_4,cycle2970_5]⟩
lemma valid_data2970 : data2970.Valid src2970 dst2970 Finset.univ := by decide +kernel

def src2971 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2971 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2971_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2971_1 : CycleData E W := ⟨3,![2,10,18,21,8],![3,4,27,38,18]⟩
def cycle2971_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2971_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2971_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2971_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2971 : PartitionData E W := ⟨6,![cycle2971_0,cycle2971_1,cycle2971_2,cycle2971_3,cycle2971_4,cycle2971_5]⟩
lemma valid_data2971 : data2971.Valid src2971 dst2971 Finset.univ := by decide +kernel

def src2972 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2972 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2972_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle2972_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,27,4]⟩
def cycle2972_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2972_3 : CycleData E W := ⟨2,![4,23,22,9],![2,8,38,18]⟩
def cycle2972_4 : CycleData E W := ⟨2,![6,17,18,11],![14,16,38,27]⟩
def cycle2972_5 : CycleData E W := ⟨3,![7,16,13,21,8],![3,16,26,28,18]⟩
def data2972 : PartitionData E W := ⟨6,![cycle2972_0,cycle2972_1,cycle2972_2,cycle2972_3,cycle2972_4,cycle2972_5]⟩
lemma valid_data2972 : data2972.Valid src2972 dst2972 Finset.univ := by decide +kernel

def src2973 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2973 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2973_0 : CycleData E W := ⟨3,![0,1,7,6,5],![2,6,3,16,14]⟩
def cycle2973_1 : CycleData E W := ⟨2,![2,14,21,8],![3,4,28,18]⟩
def cycle2973_2 : CycleData E W := ⟨3,![3,23,17,18,10],![4,8,38,16,27]⟩
def cycle2973_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2973_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2973_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2973 : PartitionData E W := ⟨6,![cycle2973_0,cycle2973_1,cycle2973_2,cycle2973_3,cycle2973_4,cycle2973_5]⟩
lemma valid_data2973 : data2973.Valid src2973 dst2973 Finset.univ := by decide +kernel

def src2974 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2974 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2974_0 : CycleData E W := ⟨2,![0,15,12,5],![2,6,26,14]⟩
def cycle2974_1 : CycleData E W := ⟨2,![1,19,10,2],![3,6,27,4]⟩
def cycle2974_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2974_3 : CycleData E W := ⟨1,![4,20,9],![2,8,18]⟩
def cycle2974_4 : CycleData E W := ⟨1,![6,18,11],![14,16,27]⟩
def cycle2974_5 : CycleData E W := ⟨2,![7,17,21,8],![3,16,38,18]⟩
def cycle2974_6 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2974 : PartitionData E W := ⟨7,![cycle2974_0,cycle2974_1,cycle2974_2,cycle2974_3,cycle2974_4,cycle2974_5,cycle2974_6]⟩
lemma valid_data2974 : data2974.Valid src2974 dst2974 Finset.univ := by decide +kernel

def src2975 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2975 : E → W := ![6,3,4,8,2,14,16,3,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2975_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle2975_1 : CycleData E W := ⟨2,![2,10,18,7],![3,4,27,16]⟩
def cycle2975_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2975_3 : CycleData E W := ⟨3,![4,23,17,6,5],![2,8,38,16,14]⟩
def cycle2975_4 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def cycle2975_5 : CycleData E W := ⟨2,![21,13,16,22],![18,28,26,38]⟩
def data2975 : PartitionData E W := ⟨6,![cycle2975_0,cycle2975_1,cycle2975_2,cycle2975_3,cycle2975_4,cycle2975_5]⟩
lemma valid_data2975 : data2975.Valid src2975 dst2975 Finset.univ := by decide +kernel

def src2976 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst2976 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2976_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2976_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2976_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2976_3 : CycleData E W := ⟨3,![4,23,16,11,5],![2,8,38,26,14]⟩
def cycle2976_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2976_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2976 : PartitionData E W := ⟨6,![cycle2976_0,cycle2976_1,cycle2976_2,cycle2976_3,cycle2976_4,cycle2976_5]⟩
lemma valid_data2976 : data2976.Valid src2976 dst2976 Finset.univ := by decide +kernel

def src2977 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst2977 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2977_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2977_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2977_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2977_3 : CycleData E W := ⟨4,![4,20,21,16,11,5],![2,8,18,38,26,14]⟩
def cycle2977_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2977_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2977 : PartitionData E W := ⟨6,![cycle2977_0,cycle2977_1,cycle2977_2,cycle2977_3,cycle2977_4,cycle2977_5]⟩
lemma valid_data2977 : data2977.Valid src2977 dst2977 Finset.univ := by decide +kernel

def src2978 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst2978 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2978_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2978_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2978_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2978_3 : CycleData E W := ⟨3,![4,23,16,11,5],![2,8,38,26,14]⟩
def cycle2978_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2978_5 : CycleData E W := ⟨3,![17,22,21,13,18],![16,38,18,28,27]⟩
def data2978 : PartitionData E W := ⟨6,![cycle2978_0,cycle2978_1,cycle2978_2,cycle2978_3,cycle2978_4,cycle2978_5]⟩
lemma valid_data2978 : data2978.Valid src2978 dst2978 Finset.univ := by decide +kernel

def src2979 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst2979 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2979_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2979_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2979_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2979_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle2979_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2979_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2979 : PartitionData E W := ⟨6,![cycle2979_0,cycle2979_1,cycle2979_2,cycle2979_3,cycle2979_4,cycle2979_5]⟩
lemma valid_data2979 : data2979.Valid src2979 dst2979 Finset.univ := by decide +kernel

def src2980 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst2980 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2980_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2980_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2980_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2980_3 : CycleData E W := ⟨4,![4,20,21,18,11,5],![2,8,18,38,26,14]⟩
def cycle2980_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2980_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2980 : PartitionData E W := ⟨6,![cycle2980_0,cycle2980_1,cycle2980_2,cycle2980_3,cycle2980_4,cycle2980_5]⟩
lemma valid_data2980 : data2980.Valid src2980 dst2980 Finset.univ := by decide +kernel

def src2981 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst2981 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2981_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2981_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2981_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2981_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,26,14]⟩
def cycle2981_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2981_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2981 : PartitionData E W := ⟨6,![cycle2981_0,cycle2981_1,cycle2981_2,cycle2981_3,cycle2981_4,cycle2981_5]⟩
lemma valid_data2981 : data2981.Valid src2981 dst2981 Finset.univ := by decide +kernel

def src2982 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst2982 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2982_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle2982_1 : CycleData E W := ⟨3,![1,19,23,20,7],![3,6,38,8,18]⟩
def cycle2982_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,27,16]⟩
def cycle2982_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle2982_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle2982_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2982 : PartitionData E W := ⟨6,![cycle2982_0,cycle2982_1,cycle2982_2,cycle2982_3,cycle2982_4,cycle2982_5]⟩
lemma valid_data2982 : data2982.Valid src2982 dst2982 Finset.univ := by decide +kernel

def src2983 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst2983 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2983_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2983_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2983_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,27,16]⟩
def cycle2983_3 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle2983_4 : CycleData E W := ⟨3,![4,23,12,16,9],![2,8,28,26,16]⟩
def cycle2983_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2983 : PartitionData E W := ⟨6,![cycle2983_0,cycle2983_1,cycle2983_2,cycle2983_3,cycle2983_4,cycle2983_5]⟩
lemma valid_data2983 : data2983.Valid src2983 dst2983 Finset.univ := by decide +kernel

def src2984 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst2984 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2984_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle2984_1 : CycleData E W := ⟨2,![1,19,22,7],![3,6,38,18]⟩
def cycle2984_2 : CycleData E W := ⟨2,![2,14,17,8],![3,4,27,16]⟩
def cycle2984_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle2984_4 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle2984_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2984 : PartitionData E W := ⟨6,![cycle2984_0,cycle2984_1,cycle2984_2,cycle2984_3,cycle2984_4,cycle2984_5]⟩
lemma valid_data2984 : data2984.Valid src2984 dst2984 Finset.univ := by decide +kernel

def src2985 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst2985 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle2985_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2985_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2985_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle2985_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2985_4 : CycleData E W := ⟨3,![7,21,12,16,8],![3,18,28,26,16]⟩
def cycle2985_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2985 : PartitionData E W := ⟨6,![cycle2985_0,cycle2985_1,cycle2985_2,cycle2985_3,cycle2985_4,cycle2985_5]⟩
lemma valid_data2985 : data2985.Valid src2985 dst2985 Finset.univ := by decide +kernel

def src2986 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst2986 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle2986_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2986_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2986_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle2986_3 : CycleData E W := ⟨3,![4,23,12,16,9],![2,8,28,26,16]⟩
def cycle2986_4 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle2986_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2986 : PartitionData E W := ⟨6,![cycle2986_0,cycle2986_1,cycle2986_2,cycle2986_3,cycle2986_4,cycle2986_5]⟩
lemma valid_data2986 : data2986.Valid src2986 dst2986 Finset.univ := by decide +kernel

def src2987 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst2987 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle2987_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,26,16]⟩
def cycle2987_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2987_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle2987_3 : CycleData E W := ⟨2,![6,21,12,11],![14,18,28,26]⟩
def cycle2987_4 : CycleData E W := ⟨2,![7,22,17,8],![3,18,38,16]⟩
def cycle2987_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2987 : PartitionData E W := ⟨6,![cycle2987_0,cycle2987_1,cycle2987_2,cycle2987_3,cycle2987_4,cycle2987_5]⟩
lemma valid_data2987 : data2987.Valid src2987 dst2987 Finset.univ := by decide +kernel

def src2988 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst2988 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2988_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2988_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2988_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle2988_3 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2988_4 : CycleData E W := ⟨3,![7,21,13,18,8],![3,18,28,27,16]⟩
def cycle2988_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2988 : PartitionData E W := ⟨6,![cycle2988_0,cycle2988_1,cycle2988_2,cycle2988_3,cycle2988_4,cycle2988_5]⟩
lemma valid_data2988 : data2988.Valid src2988 dst2988 Finset.univ := by decide +kernel

def src2989 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst2989 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2989_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2989_1 : CycleData E W := ⟨2,![1,19,14,2],![3,6,27,4]⟩
def cycle2989_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle2989_3 : CycleData E W := ⟨3,![4,23,13,18,9],![2,8,28,27,16]⟩
def cycle2989_4 : CycleData E W := ⟨2,![7,21,17,8],![3,18,38,16]⟩
def cycle2989_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2989 : PartitionData E W := ⟨6,![cycle2989_0,cycle2989_1,cycle2989_2,cycle2989_3,cycle2989_4,cycle2989_5]⟩
lemma valid_data2989 : data2989.Valid src2989 dst2989 Finset.univ := by decide +kernel

def src2990 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst2990 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2990_0 : CycleData E W := ⟨2,![0,15,11,5],![2,6,26,14]⟩
def cycle2990_1 : CycleData E W := ⟨2,![1,19,18,8],![3,6,27,16]⟩
def cycle2990_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2990_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle2990_4 : CycleData E W := ⟨2,![4,23,17,9],![2,8,38,16]⟩
def cycle2990_5 : CycleData E W := ⟨2,![21,12,16,22],![18,28,26,38]⟩
def data2990 : PartitionData E W := ⟨6,![cycle2990_0,cycle2990_1,cycle2990_2,cycle2990_3,cycle2990_4,cycle2990_5]⟩
lemma valid_data2990 : data2990.Valid src2990 dst2990 Finset.univ := by decide +kernel

def src2991 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst2991 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2991_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle2991_1 : CycleData E W := ⟨2,![1,15,14,2],![3,6,27,4]⟩
def cycle2991_2 : CycleData E W := ⟨2,![3,20,6,10],![4,8,18,14]⟩
def cycle2991_3 : CycleData E W := ⟨2,![5,11,17,9],![2,14,26,16]⟩
def cycle2991_4 : CycleData E W := ⟨3,![7,21,13,16,8],![3,18,28,27,16]⟩
def cycle2991_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2991 : PartitionData E W := ⟨6,![cycle2991_0,cycle2991_1,cycle2991_2,cycle2991_3,cycle2991_4,cycle2991_5]⟩
lemma valid_data2991 : data2991.Valid src2991 dst2991 Finset.univ := by decide +kernel

def src2992 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst2992 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2992_0 : CycleData E W := ⟨2,![0,15,16,9],![2,6,27,16]⟩
def cycle2992_1 : CycleData E W := ⟨2,![1,19,21,7],![3,6,38,18]⟩
def cycle2992_2 : CycleData E W := ⟨3,![2,10,11,17,8],![3,4,14,26,16]⟩
def cycle2992_3 : CycleData E W := ⟨2,![3,23,13,14],![4,8,28,27]⟩
def cycle2992_4 : CycleData E W := ⟨2,![4,20,6,5],![2,8,18,14]⟩
def cycle2992_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2992 : PartitionData E W := ⟨6,![cycle2992_0,cycle2992_1,cycle2992_2,cycle2992_3,cycle2992_4,cycle2992_5]⟩
lemma valid_data2992 : data2992.Valid src2992 dst2992 Finset.univ := by decide +kernel

def src2993 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst2993 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2993_0 : CycleData E W := ⟨2,![0,19,23,4],![2,6,38,8]⟩
def cycle2993_1 : CycleData E W := ⟨2,![1,15,16,8],![3,6,27,16]⟩
def cycle2993_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2993_3 : CycleData E W := ⟨2,![3,20,13,14],![4,8,28,27]⟩
def cycle2993_4 : CycleData E W := ⟨2,![5,11,17,9],![2,14,26,16]⟩
def cycle2993_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,26,38]⟩
def data2993 : PartitionData E W := ⟨6,![cycle2993_0,cycle2993_1,cycle2993_2,cycle2993_3,cycle2993_4,cycle2993_5]⟩
lemma valid_data2993 : data2993.Valid src2993 dst2993 Finset.univ := by decide +kernel

def src2994 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst2994 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2994_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2994_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2994_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2994_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle2994_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2994_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2994 : PartitionData E W := ⟨6,![cycle2994_0,cycle2994_1,cycle2994_2,cycle2994_3,cycle2994_4,cycle2994_5]⟩
lemma valid_data2994 : data2994.Valid src2994 dst2994 Finset.univ := by decide +kernel

def src2995 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst2995 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2995_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2995_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2995_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2995_3 : CycleData E W := ⟨4,![4,20,21,18,11,5],![2,8,18,38,27,14]⟩
def cycle2995_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2995_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2995 : PartitionData E W := ⟨6,![cycle2995_0,cycle2995_1,cycle2995_2,cycle2995_3,cycle2995_4,cycle2995_5]⟩
lemma valid_data2995 : data2995.Valid src2995 dst2995 Finset.univ := by decide +kernel

def src2996 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst2996 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2996_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2996_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2996_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2996_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle2996_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2996_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2996 : PartitionData E W := ⟨6,![cycle2996_0,cycle2996_1,cycle2996_2,cycle2996_3,cycle2996_4,cycle2996_5]⟩
lemma valid_data2996 : data2996.Valid src2996 dst2996 Finset.univ := by decide +kernel

def src2997 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst2997 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2997_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2997_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2997_2 : CycleData E W := ⟨2,![3,20,21,14],![4,8,18,28]⟩
def cycle2997_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle2997_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2997_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2997 : PartitionData E W := ⟨6,![cycle2997_0,cycle2997_1,cycle2997_2,cycle2997_3,cycle2997_4,cycle2997_5]⟩
lemma valid_data2997 : data2997.Valid src2997 dst2997 Finset.univ := by decide +kernel

def src2998 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst2998 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2998_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2998_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2998_2 : CycleData E W := ⟨1,![3,23,14],![4,8,28]⟩
def cycle2998_3 : CycleData E W := ⟨4,![4,20,21,18,11,5],![2,8,18,38,27,14]⟩
def cycle2998_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2998_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2998 : PartitionData E W := ⟨6,![cycle2998_0,cycle2998_1,cycle2998_2,cycle2998_3,cycle2998_4,cycle2998_5]⟩
lemma valid_data2998 : data2998.Valid src2998 dst2998 Finset.univ := by decide +kernel

def src2999 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst2999 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2999_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,16]⟩
def cycle2999_1 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle2999_2 : CycleData E W := ⟨1,![3,20,14],![4,8,28]⟩
def cycle2999_3 : CycleData E W := ⟨3,![4,23,18,11,5],![2,8,38,27,14]⟩
def cycle2999_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2999_5 : CycleData E W := ⟨3,![16,13,21,22,17],![16,26,28,18,38]⟩
def data2999 : PartitionData E W := ⟨6,![cycle2999_0,cycle2999_1,cycle2999_2,cycle2999_3,cycle2999_4,cycle2999_5]⟩
lemma valid_data2999 : data2999.Valid src2999 dst2999 Finset.univ := by decide +kernel

def lookupB14 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data2800 else (if j < 2 then data2801 else data2802)) else (if j < 4 then data2803 else (if j < 5 then data2804 else data2805))) else (if j < 9 then (if j < 7 then data2806 else (if j < 8 then data2807 else data2808)) else (if j < 10 then data2809 else (if j < 11 then data2810 else data2811)))) else (if j < 18 then (if j < 15 then (if j < 13 then data2812 else (if j < 14 then data2813 else data2814)) else (if j < 16 then data2815 else (if j < 17 then data2816 else data2817))) else (if j < 21 then (if j < 19 then data2818 else (if j < 20 then data2819 else data2820)) else (if j < 23 then (if j < 22 then data2821 else data2822) else (if j < 24 then data2823 else data2824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data2825 else (if j < 27 then data2826 else data2827)) else (if j < 29 then data2828 else (if j < 30 then data2829 else data2830))) else (if j < 34 then (if j < 32 then data2831 else (if j < 33 then data2832 else data2833)) else (if j < 35 then data2834 else (if j < 36 then data2835 else data2836)))) else (if j < 43 then (if j < 40 then (if j < 38 then data2837 else (if j < 39 then data2838 else data2839)) else (if j < 41 then data2840 else (if j < 42 then data2841 else data2842))) else (if j < 46 then (if j < 44 then data2843 else (if j < 45 then data2844 else data2845)) else (if j < 48 then (if j < 47 then data2846 else data2847) else (if j < 49 then data2848 else data2849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data2850 else (if j < 52 then data2851 else data2852)) else (if j < 54 then data2853 else (if j < 55 then data2854 else data2855))) else (if j < 59 then (if j < 57 then data2856 else (if j < 58 then data2857 else data2858)) else (if j < 60 then data2859 else (if j < 61 then data2860 else data2861)))) else (if j < 68 then (if j < 65 then (if j < 63 then data2862 else (if j < 64 then data2863 else data2864)) else (if j < 66 then data2865 else (if j < 67 then data2866 else data2867))) else (if j < 71 then (if j < 69 then data2868 else (if j < 70 then data2869 else data2870)) else (if j < 73 then (if j < 72 then data2871 else data2872) else (if j < 74 then data2873 else data2874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data2875 else (if j < 77 then data2876 else data2877)) else (if j < 79 then data2878 else (if j < 80 then data2879 else data2880))) else (if j < 84 then (if j < 82 then data2881 else (if j < 83 then data2882 else data2883)) else (if j < 85 then data2884 else (if j < 86 then data2885 else data2886)))) else (if j < 93 then (if j < 90 then (if j < 88 then data2887 else (if j < 89 then data2888 else data2889)) else (if j < 91 then data2890 else (if j < 92 then data2891 else data2892))) else (if j < 96 then (if j < 94 then data2893 else (if j < 95 then data2894 else data2895)) else (if j < 98 then (if j < 97 then data2896 else data2897) else (if j < 99 then data2898 else data2899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data2900 else (if j < 102 then data2901 else data2902)) else (if j < 104 then data2903 else (if j < 105 then data2904 else data2905))) else (if j < 109 then (if j < 107 then data2906 else (if j < 108 then data2907 else data2908)) else (if j < 110 then data2909 else (if j < 111 then data2910 else data2911)))) else (if j < 118 then (if j < 115 then (if j < 113 then data2912 else (if j < 114 then data2913 else data2914)) else (if j < 116 then data2915 else (if j < 117 then data2916 else data2917))) else (if j < 121 then (if j < 119 then data2918 else (if j < 120 then data2919 else data2920)) else (if j < 123 then (if j < 122 then data2921 else data2922) else (if j < 124 then data2923 else data2924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data2925 else (if j < 127 then data2926 else data2927)) else (if j < 129 then data2928 else (if j < 130 then data2929 else data2930))) else (if j < 134 then (if j < 132 then data2931 else (if j < 133 then data2932 else data2933)) else (if j < 135 then data2934 else (if j < 136 then data2935 else data2936)))) else (if j < 143 then (if j < 140 then (if j < 138 then data2937 else (if j < 139 then data2938 else data2939)) else (if j < 141 then data2940 else (if j < 142 then data2941 else data2942))) else (if j < 146 then (if j < 144 then data2943 else (if j < 145 then data2944 else data2945)) else (if j < 148 then (if j < 147 then data2946 else data2947) else (if j < 149 then data2948 else data2949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data2950 else (if j < 152 then data2951 else data2952)) else (if j < 154 then data2953 else (if j < 155 then data2954 else data2955))) else (if j < 159 then (if j < 157 then data2956 else (if j < 158 then data2957 else data2958)) else (if j < 160 then data2959 else (if j < 161 then data2960 else data2961)))) else (if j < 168 then (if j < 165 then (if j < 163 then data2962 else (if j < 164 then data2963 else data2964)) else (if j < 166 then data2965 else (if j < 167 then data2966 else data2967))) else (if j < 171 then (if j < 169 then data2968 else (if j < 170 then data2969 else data2970)) else (if j < 173 then (if j < 172 then data2971 else data2972) else (if j < 174 then data2973 else data2974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data2975 else (if j < 177 then data2976 else data2977)) else (if j < 179 then data2978 else (if j < 180 then data2979 else data2980))) else (if j < 184 then (if j < 182 then data2981 else (if j < 183 then data2982 else data2983)) else (if j < 185 then data2984 else (if j < 186 then data2985 else data2986)))) else (if j < 193 then (if j < 190 then (if j < 188 then data2987 else (if j < 189 then data2988 else data2989)) else (if j < 191 then data2990 else (if j < 192 then data2991 else data2992))) else (if j < 196 then (if j < 194 then data2993 else (if j < 195 then data2994 else data2995)) else (if j < 198 then (if j < 197 then data2996 else data2997) else (if j < 199 then data2998 else data2999))))))))

def srcTableB14 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src2800 else (if j < 2 then src2801 else src2802)) else (if j < 4 then src2803 else (if j < 5 then src2804 else src2805))) else (if j < 9 then (if j < 7 then src2806 else (if j < 8 then src2807 else src2808)) else (if j < 10 then src2809 else (if j < 11 then src2810 else src2811)))) else (if j < 18 then (if j < 15 then (if j < 13 then src2812 else (if j < 14 then src2813 else src2814)) else (if j < 16 then src2815 else (if j < 17 then src2816 else src2817))) else (if j < 21 then (if j < 19 then src2818 else (if j < 20 then src2819 else src2820)) else (if j < 23 then (if j < 22 then src2821 else src2822) else (if j < 24 then src2823 else src2824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src2825 else (if j < 27 then src2826 else src2827)) else (if j < 29 then src2828 else (if j < 30 then src2829 else src2830))) else (if j < 34 then (if j < 32 then src2831 else (if j < 33 then src2832 else src2833)) else (if j < 35 then src2834 else (if j < 36 then src2835 else src2836)))) else (if j < 43 then (if j < 40 then (if j < 38 then src2837 else (if j < 39 then src2838 else src2839)) else (if j < 41 then src2840 else (if j < 42 then src2841 else src2842))) else (if j < 46 then (if j < 44 then src2843 else (if j < 45 then src2844 else src2845)) else (if j < 48 then (if j < 47 then src2846 else src2847) else (if j < 49 then src2848 else src2849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src2850 else (if j < 52 then src2851 else src2852)) else (if j < 54 then src2853 else (if j < 55 then src2854 else src2855))) else (if j < 59 then (if j < 57 then src2856 else (if j < 58 then src2857 else src2858)) else (if j < 60 then src2859 else (if j < 61 then src2860 else src2861)))) else (if j < 68 then (if j < 65 then (if j < 63 then src2862 else (if j < 64 then src2863 else src2864)) else (if j < 66 then src2865 else (if j < 67 then src2866 else src2867))) else (if j < 71 then (if j < 69 then src2868 else (if j < 70 then src2869 else src2870)) else (if j < 73 then (if j < 72 then src2871 else src2872) else (if j < 74 then src2873 else src2874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src2875 else (if j < 77 then src2876 else src2877)) else (if j < 79 then src2878 else (if j < 80 then src2879 else src2880))) else (if j < 84 then (if j < 82 then src2881 else (if j < 83 then src2882 else src2883)) else (if j < 85 then src2884 else (if j < 86 then src2885 else src2886)))) else (if j < 93 then (if j < 90 then (if j < 88 then src2887 else (if j < 89 then src2888 else src2889)) else (if j < 91 then src2890 else (if j < 92 then src2891 else src2892))) else (if j < 96 then (if j < 94 then src2893 else (if j < 95 then src2894 else src2895)) else (if j < 98 then (if j < 97 then src2896 else src2897) else (if j < 99 then src2898 else src2899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src2900 else (if j < 102 then src2901 else src2902)) else (if j < 104 then src2903 else (if j < 105 then src2904 else src2905))) else (if j < 109 then (if j < 107 then src2906 else (if j < 108 then src2907 else src2908)) else (if j < 110 then src2909 else (if j < 111 then src2910 else src2911)))) else (if j < 118 then (if j < 115 then (if j < 113 then src2912 else (if j < 114 then src2913 else src2914)) else (if j < 116 then src2915 else (if j < 117 then src2916 else src2917))) else (if j < 121 then (if j < 119 then src2918 else (if j < 120 then src2919 else src2920)) else (if j < 123 then (if j < 122 then src2921 else src2922) else (if j < 124 then src2923 else src2924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src2925 else (if j < 127 then src2926 else src2927)) else (if j < 129 then src2928 else (if j < 130 then src2929 else src2930))) else (if j < 134 then (if j < 132 then src2931 else (if j < 133 then src2932 else src2933)) else (if j < 135 then src2934 else (if j < 136 then src2935 else src2936)))) else (if j < 143 then (if j < 140 then (if j < 138 then src2937 else (if j < 139 then src2938 else src2939)) else (if j < 141 then src2940 else (if j < 142 then src2941 else src2942))) else (if j < 146 then (if j < 144 then src2943 else (if j < 145 then src2944 else src2945)) else (if j < 148 then (if j < 147 then src2946 else src2947) else (if j < 149 then src2948 else src2949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src2950 else (if j < 152 then src2951 else src2952)) else (if j < 154 then src2953 else (if j < 155 then src2954 else src2955))) else (if j < 159 then (if j < 157 then src2956 else (if j < 158 then src2957 else src2958)) else (if j < 160 then src2959 else (if j < 161 then src2960 else src2961)))) else (if j < 168 then (if j < 165 then (if j < 163 then src2962 else (if j < 164 then src2963 else src2964)) else (if j < 166 then src2965 else (if j < 167 then src2966 else src2967))) else (if j < 171 then (if j < 169 then src2968 else (if j < 170 then src2969 else src2970)) else (if j < 173 then (if j < 172 then src2971 else src2972) else (if j < 174 then src2973 else src2974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src2975 else (if j < 177 then src2976 else src2977)) else (if j < 179 then src2978 else (if j < 180 then src2979 else src2980))) else (if j < 184 then (if j < 182 then src2981 else (if j < 183 then src2982 else src2983)) else (if j < 185 then src2984 else (if j < 186 then src2985 else src2986)))) else (if j < 193 then (if j < 190 then (if j < 188 then src2987 else (if j < 189 then src2988 else src2989)) else (if j < 191 then src2990 else (if j < 192 then src2991 else src2992))) else (if j < 196 then (if j < 194 then src2993 else (if j < 195 then src2994 else src2995)) else (if j < 198 then (if j < 197 then src2996 else src2997) else (if j < 199 then src2998 else src2999))))))))

def dstTableB14 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst2800 else (if j < 2 then dst2801 else dst2802)) else (if j < 4 then dst2803 else (if j < 5 then dst2804 else dst2805))) else (if j < 9 then (if j < 7 then dst2806 else (if j < 8 then dst2807 else dst2808)) else (if j < 10 then dst2809 else (if j < 11 then dst2810 else dst2811)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst2812 else (if j < 14 then dst2813 else dst2814)) else (if j < 16 then dst2815 else (if j < 17 then dst2816 else dst2817))) else (if j < 21 then (if j < 19 then dst2818 else (if j < 20 then dst2819 else dst2820)) else (if j < 23 then (if j < 22 then dst2821 else dst2822) else (if j < 24 then dst2823 else dst2824))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst2825 else (if j < 27 then dst2826 else dst2827)) else (if j < 29 then dst2828 else (if j < 30 then dst2829 else dst2830))) else (if j < 34 then (if j < 32 then dst2831 else (if j < 33 then dst2832 else dst2833)) else (if j < 35 then dst2834 else (if j < 36 then dst2835 else dst2836)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst2837 else (if j < 39 then dst2838 else dst2839)) else (if j < 41 then dst2840 else (if j < 42 then dst2841 else dst2842))) else (if j < 46 then (if j < 44 then dst2843 else (if j < 45 then dst2844 else dst2845)) else (if j < 48 then (if j < 47 then dst2846 else dst2847) else (if j < 49 then dst2848 else dst2849)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst2850 else (if j < 52 then dst2851 else dst2852)) else (if j < 54 then dst2853 else (if j < 55 then dst2854 else dst2855))) else (if j < 59 then (if j < 57 then dst2856 else (if j < 58 then dst2857 else dst2858)) else (if j < 60 then dst2859 else (if j < 61 then dst2860 else dst2861)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst2862 else (if j < 64 then dst2863 else dst2864)) else (if j < 66 then dst2865 else (if j < 67 then dst2866 else dst2867))) else (if j < 71 then (if j < 69 then dst2868 else (if j < 70 then dst2869 else dst2870)) else (if j < 73 then (if j < 72 then dst2871 else dst2872) else (if j < 74 then dst2873 else dst2874))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst2875 else (if j < 77 then dst2876 else dst2877)) else (if j < 79 then dst2878 else (if j < 80 then dst2879 else dst2880))) else (if j < 84 then (if j < 82 then dst2881 else (if j < 83 then dst2882 else dst2883)) else (if j < 85 then dst2884 else (if j < 86 then dst2885 else dst2886)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst2887 else (if j < 89 then dst2888 else dst2889)) else (if j < 91 then dst2890 else (if j < 92 then dst2891 else dst2892))) else (if j < 96 then (if j < 94 then dst2893 else (if j < 95 then dst2894 else dst2895)) else (if j < 98 then (if j < 97 then dst2896 else dst2897) else (if j < 99 then dst2898 else dst2899))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst2900 else (if j < 102 then dst2901 else dst2902)) else (if j < 104 then dst2903 else (if j < 105 then dst2904 else dst2905))) else (if j < 109 then (if j < 107 then dst2906 else (if j < 108 then dst2907 else dst2908)) else (if j < 110 then dst2909 else (if j < 111 then dst2910 else dst2911)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst2912 else (if j < 114 then dst2913 else dst2914)) else (if j < 116 then dst2915 else (if j < 117 then dst2916 else dst2917))) else (if j < 121 then (if j < 119 then dst2918 else (if j < 120 then dst2919 else dst2920)) else (if j < 123 then (if j < 122 then dst2921 else dst2922) else (if j < 124 then dst2923 else dst2924))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst2925 else (if j < 127 then dst2926 else dst2927)) else (if j < 129 then dst2928 else (if j < 130 then dst2929 else dst2930))) else (if j < 134 then (if j < 132 then dst2931 else (if j < 133 then dst2932 else dst2933)) else (if j < 135 then dst2934 else (if j < 136 then dst2935 else dst2936)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst2937 else (if j < 139 then dst2938 else dst2939)) else (if j < 141 then dst2940 else (if j < 142 then dst2941 else dst2942))) else (if j < 146 then (if j < 144 then dst2943 else (if j < 145 then dst2944 else dst2945)) else (if j < 148 then (if j < 147 then dst2946 else dst2947) else (if j < 149 then dst2948 else dst2949)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst2950 else (if j < 152 then dst2951 else dst2952)) else (if j < 154 then dst2953 else (if j < 155 then dst2954 else dst2955))) else (if j < 159 then (if j < 157 then dst2956 else (if j < 158 then dst2957 else dst2958)) else (if j < 160 then dst2959 else (if j < 161 then dst2960 else dst2961)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst2962 else (if j < 164 then dst2963 else dst2964)) else (if j < 166 then dst2965 else (if j < 167 then dst2966 else dst2967))) else (if j < 171 then (if j < 169 then dst2968 else (if j < 170 then dst2969 else dst2970)) else (if j < 173 then (if j < 172 then dst2971 else dst2972) else (if j < 174 then dst2973 else dst2974))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst2975 else (if j < 177 then dst2976 else dst2977)) else (if j < 179 then dst2978 else (if j < 180 then dst2979 else dst2980))) else (if j < 184 then (if j < 182 then dst2981 else (if j < 183 then dst2982 else dst2983)) else (if j < 185 then dst2984 else (if j < 186 then dst2985 else dst2986)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst2987 else (if j < 189 then dst2988 else dst2989)) else (if j < 191 then dst2990 else (if j < 192 then dst2991 else dst2992))) else (if j < 196 then (if j < 194 then dst2993 else (if j < 195 then dst2994 else dst2995)) else (if j < 198 then (if j < 197 then dst2996 else dst2997) else (if j < 199 then dst2998 else dst2999))))))))

def caseB14 (i : Fin 200) : Cases := ⟨2800 + i.val,by have := i.isLt; omega⟩
lemma tableB14_valid (i : Fin 200) :
    (lookupB14 i.val).Valid (srcTableB14 i.val) (dstTableB14 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data2800
  · exact valid_data2801
  · exact valid_data2802
  · exact valid_data2803
  · exact valid_data2804
  · exact valid_data2805
  · exact valid_data2806
  · exact valid_data2807
  · exact valid_data2808
  · exact valid_data2809
  · exact valid_data2810
  · exact valid_data2811
  · exact valid_data2812
  · exact valid_data2813
  · exact valid_data2814
  · exact valid_data2815
  · exact valid_data2816
  · exact valid_data2817
  · exact valid_data2818
  · exact valid_data2819
  · exact valid_data2820
  · exact valid_data2821
  · exact valid_data2822
  · exact valid_data2823
  · exact valid_data2824
  · exact valid_data2825
  · exact valid_data2826
  · exact valid_data2827
  · exact valid_data2828
  · exact valid_data2829
  · exact valid_data2830
  · exact valid_data2831
  · exact valid_data2832
  · exact valid_data2833
  · exact valid_data2834
  · exact valid_data2835
  · exact valid_data2836
  · exact valid_data2837
  · exact valid_data2838
  · exact valid_data2839
  · exact valid_data2840
  · exact valid_data2841
  · exact valid_data2842
  · exact valid_data2843
  · exact valid_data2844
  · exact valid_data2845
  · exact valid_data2846
  · exact valid_data2847
  · exact valid_data2848
  · exact valid_data2849
  · exact valid_data2850
  · exact valid_data2851
  · exact valid_data2852
  · exact valid_data2853
  · exact valid_data2854
  · exact valid_data2855
  · exact valid_data2856
  · exact valid_data2857
  · exact valid_data2858
  · exact valid_data2859
  · exact valid_data2860
  · exact valid_data2861
  · exact valid_data2862
  · exact valid_data2863
  · exact valid_data2864
  · exact valid_data2865
  · exact valid_data2866
  · exact valid_data2867
  · exact valid_data2868
  · exact valid_data2869
  · exact valid_data2870
  · exact valid_data2871
  · exact valid_data2872
  · exact valid_data2873
  · exact valid_data2874
  · exact valid_data2875
  · exact valid_data2876
  · exact valid_data2877
  · exact valid_data2878
  · exact valid_data2879
  · exact valid_data2880
  · exact valid_data2881
  · exact valid_data2882
  · exact valid_data2883
  · exact valid_data2884
  · exact valid_data2885
  · exact valid_data2886
  · exact valid_data2887
  · exact valid_data2888
  · exact valid_data2889
  · exact valid_data2890
  · exact valid_data2891
  · exact valid_data2892
  · exact valid_data2893
  · exact valid_data2894
  · exact valid_data2895
  · exact valid_data2896
  · exact valid_data2897
  · exact valid_data2898
  · exact valid_data2899
  · exact valid_data2900
  · exact valid_data2901
  · exact valid_data2902
  · exact valid_data2903
  · exact valid_data2904
  · exact valid_data2905
  · exact valid_data2906
  · exact valid_data2907
  · exact valid_data2908
  · exact valid_data2909
  · exact valid_data2910
  · exact valid_data2911
  · exact valid_data2912
  · exact valid_data2913
  · exact valid_data2914
  · exact valid_data2915
  · exact valid_data2916
  · exact valid_data2917
  · exact valid_data2918
  · exact valid_data2919
  · exact valid_data2920
  · exact valid_data2921
  · exact valid_data2922
  · exact valid_data2923
  · exact valid_data2924
  · exact valid_data2925
  · exact valid_data2926
  · exact valid_data2927
  · exact valid_data2928
  · exact valid_data2929
  · exact valid_data2930
  · exact valid_data2931
  · exact valid_data2932
  · exact valid_data2933
  · exact valid_data2934
  · exact valid_data2935
  · exact valid_data2936
  · exact valid_data2937
  · exact valid_data2938
  · exact valid_data2939
  · exact valid_data2940
  · exact valid_data2941
  · exact valid_data2942
  · exact valid_data2943
  · exact valid_data2944
  · exact valid_data2945
  · exact valid_data2946
  · exact valid_data2947
  · exact valid_data2948
  · exact valid_data2949
  · exact valid_data2950
  · exact valid_data2951
  · exact valid_data2952
  · exact valid_data2953
  · exact valid_data2954
  · exact valid_data2955
  · exact valid_data2956
  · exact valid_data2957
  · exact valid_data2958
  · exact valid_data2959
  · exact valid_data2960
  · exact valid_data2961
  · exact valid_data2962
  · exact valid_data2963
  · exact valid_data2964
  · exact valid_data2965
  · exact valid_data2966
  · exact valid_data2967
  · exact valid_data2968
  · exact valid_data2969
  · exact valid_data2970
  · exact valid_data2971
  · exact valid_data2972
  · exact valid_data2973
  · exact valid_data2974
  · exact valid_data2975
  · exact valid_data2976
  · exact valid_data2977
  · exact valid_data2978
  · exact valid_data2979
  · exact valid_data2980
  · exact valid_data2981
  · exact valid_data2982
  · exact valid_data2983
  · exact valid_data2984
  · exact valid_data2985
  · exact valid_data2986
  · exact valid_data2987
  · exact valid_data2988
  · exact valid_data2989
  · exact valid_data2990
  · exact valid_data2991
  · exact valid_data2992
  · exact valid_data2993
  · exact valid_data2994
  · exact valid_data2995
  · exact valid_data2996
  · exact valid_data2997
  · exact valid_data2998
  · exact valid_data2999

lemma srcB14_row : ∀ (i : Fin 200) (e : E),
    srcTableB14 i.val e = caseSource (caseB14 i) e := by decide +kernel

lemma dstB14_row : ∀ (i : Fin 200) (e : E),
    dstTableB14 i.val e = caseTarget (caseB14 i) e := by decide +kernel

lemma sizeB14 : ∀ i : Fin 200, (lookupB14 i.val).size ≤ 5 →
    (lookupB14 i.val).size = 2 ∧
      (⟨caseKey (caseB14 i),caseKey_lt (caseB14 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB14 (i : Fin 200) : Certificate (caseB14 i) := by
  refine ⟨lookupB14 i.val,?_,sizeB14 i⟩
  have hv := tableB14_valid i
  rw [funext (srcB14_row i),funext (dstB14_row i)] at hv
  exact hv
lemma certificateInterval14 : FiniteIntervals.Covers CertificateAt 2800 3000 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 2800 200 (fun i _ => certificateB14 i)
#print axioms certificateInterval14
end Erdos184Work.FiveRows3

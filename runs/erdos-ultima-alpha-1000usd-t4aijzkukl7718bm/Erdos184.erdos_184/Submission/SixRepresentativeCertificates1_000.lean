import Submission.SixRepresentativeCertificates1Base
namespace Erdos184Work.SixRepresentativeCertificates1
open PureSixRowModel1 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,16,30,32,34,6,18,44,30,46,8,20,44,58,32,10,34,22,58,46]
def dst0 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,16,30,32,34,4,18,44,30,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle0_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle0_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle0_2 : CycleData E W := ⟨3,![2,21,20,13,12],![4,6,46,30,16]⟩
def cycle0_3 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle0_4 : CycleData E W := ⟨2,![10,29,24,18],![18,22,58,44]⟩
def cycle0_5 : CycleData E W := ⟨3,![22,23,19,14,26],![8,20,44,30,32]⟩
def cycle0_6 : CycleData E W := ⟨3,![27,15,25,30,31],![10,34,32,58,46]⟩
def data0 : PartitionData E W := ⟨7,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4,cycle0_5,cycle0_6]⟩
lemma valid0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel
lemma src_eq0 : src0 = src (unkey (representativeKey 0)) := by decide +kernel
lemma dst_eq0 : dst0 = dst (unkey (representativeKey 0)) := by decide +kernel
lemma certificate0 : Certificate 0 := by
  refine ⟨data0,?_,?_⟩
  · rw [← src_eq0,← dst_eq0]
    exact valid0
  · decide +kernel

def src1 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,16,30,32,34,6,18,44,30,46,8,20,58,44,32,10,34,22,58,46]
def dst1 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,16,30,32,34,4,18,44,30,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle1_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle1_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle1_2 : CycleData E W := ⟨3,![2,21,20,13,12],![4,6,46,30,16]⟩
def cycle1_3 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle1_4 : CycleData E W := ⟨2,![10,29,24,18],![18,22,58,44]⟩
def cycle1_5 : CycleData E W := ⟨1,![14,25,19],![30,32,44]⟩
def cycle1_6 : CycleData E W := ⟨5,![22,23,30,31,27,15,26],![8,20,58,46,10,34,32]⟩
def data1 : PartitionData E W := ⟨7,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4,cycle1_5,cycle1_6]⟩
lemma valid1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel
lemma src_eq1 : src1 = src (unkey (representativeKey 1)) := by decide +kernel
lemma dst_eq1 : dst1 = dst (unkey (representativeKey 1)) := by decide +kernel
lemma certificate1 : Certificate 1 := by
  refine ⟨data1,?_,?_⟩
  · rw [← src_eq1,← dst_eq1]
    exact valid1
  · decide +kernel

def src2 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,16,30,32,34,6,18,44,30,46,8,32,58,20,44,10,34,22,58,46]
def dst2 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,16,30,32,34,4,18,44,30,46,6,32,58,20,44,8,34,22,58,46,10]
def cycle2_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle2_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle2_2 : CycleData E W := ⟨3,![2,21,20,13,12],![4,6,46,30,16]⟩
def cycle2_3 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle2_4 : CycleData E W := ⟨3,![10,29,24,25,18],![18,22,58,20,44]⟩
def cycle2_5 : CycleData E W := ⟨2,![22,14,19,26],![8,32,30,44]⟩
def cycle2_6 : CycleData E W := ⟨3,![27,15,23,30,31],![10,34,32,58,46]⟩
def data2 : PartitionData E W := ⟨7,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4,cycle2_5,cycle2_6]⟩
lemma valid2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel
lemma src_eq2 : src2 = src (unkey (representativeKey 2)) := by decide +kernel
lemma dst_eq2 : dst2 = dst (unkey (representativeKey 2)) := by decide +kernel
lemma certificate2 : Certificate 2 := by
  refine ⟨data2,?_,?_⟩
  · rw [← src_eq2,← dst_eq2]
    exact valid2
  · decide +kernel

def src3 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,16,30,32,34,6,44,18,30,46,8,20,44,58,32,10,34,22,58,46]
def dst3 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,16,30,32,34,4,44,18,30,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle3_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle3_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle3_2 : CycleData E W := ⟨3,![2,21,20,13,12],![4,6,46,30,16]⟩
def cycle3_3 : CycleData E W := ⟨2,![3,22,23,17],![6,8,20,44]⟩
def cycle3_4 : CycleData E W := ⟨4,![5,4,26,14,19,11],![2,10,8,32,30,18]⟩
def cycle3_5 : CycleData E W := ⟨2,![10,29,24,18],![18,22,58,44]⟩
def cycle3_6 : CycleData E W := ⟨3,![27,15,25,30,31],![10,34,32,58,46]⟩
def data3 : PartitionData E W := ⟨7,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4,cycle3_5,cycle3_6]⟩
lemma valid3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel
lemma src_eq3 : src3 = src (unkey (representativeKey 3)) := by decide +kernel
lemma dst_eq3 : dst3 = dst (unkey (representativeKey 3)) := by decide +kernel
lemma certificate3 : Certificate 3 := by
  refine ⟨data3,?_,?_⟩
  · rw [← src_eq3,← dst_eq3]
    exact valid3
  · decide +kernel

def src4 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,16,30,32,34,6,44,18,30,46,8,20,58,44,32,10,34,22,58,46]
def dst4 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,16,30,32,34,4,44,18,30,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle4_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle4_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle4_2 : CycleData E W := ⟨3,![2,21,20,13,12],![4,6,46,30,16]⟩
def cycle4_3 : CycleData E W := ⟨3,![3,22,23,24,17],![6,8,20,58,44]⟩
def cycle4_4 : CycleData E W := ⟨2,![4,27,15,26],![8,10,34,32]⟩
def cycle4_5 : CycleData E W := ⟨4,![5,31,30,29,10,11],![2,10,46,58,22,18]⟩
def cycle4_6 : CycleData E W := ⟨2,![18,25,14,19],![18,44,32,30]⟩
def data4 : PartitionData E W := ⟨7,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4,cycle4_5,cycle4_6]⟩
lemma valid4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel
lemma src_eq4 : src4 = src (unkey (representativeKey 4)) := by decide +kernel
lemma dst_eq4 : dst4 = dst (unkey (representativeKey 4)) := by decide +kernel
lemma certificate4 : Certificate 4 := by
  refine ⟨data4,?_,?_⟩
  · rw [← src_eq4,← dst_eq4]
    exact valid4
  · decide +kernel

def src5 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,16,30,32,34,6,44,18,30,46,8,32,58,20,44,10,34,22,58,46]
def dst5 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,16,30,32,34,4,44,18,30,46,6,32,58,20,44,8,34,22,58,46,10]
def cycle5_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle5_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle5_2 : CycleData E W := ⟨3,![2,21,20,13,12],![4,6,46,30,16]⟩
def cycle5_3 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle5_4 : CycleData E W := ⟨4,![5,4,22,14,19,11],![2,10,8,32,30,18]⟩
def cycle5_5 : CycleData E W := ⟨3,![10,29,24,25,18],![18,22,58,20,44]⟩
def cycle5_6 : CycleData E W := ⟨3,![27,15,23,30,31],![10,34,32,58,46]⟩
def data5 : PartitionData E W := ⟨7,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4,cycle5_5,cycle5_6]⟩
lemma valid5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel
lemma src_eq5 : src5 = src (unkey (representativeKey 5)) := by decide +kernel
lemma dst_eq5 : dst5 = dst (unkey (representativeKey 5)) := by decide +kernel
lemma certificate5 : Certificate 5 := by
  refine ⟨data5,?_,?_⟩
  · rw [← src_eq5,← dst_eq5]
    exact valid5
  · decide +kernel

def src6 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,30,16,32,34,6,18,44,30,46,8,20,44,58,32,10,34,22,58,46]
def dst6 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,30,16,32,34,4,18,44,30,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle6_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle6_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle6_2 : CycleData E W := ⟨2,![2,21,20,12],![4,6,46,30]⟩
def cycle6_3 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle6_4 : CycleData E W := ⟨2,![10,29,24,18],![18,22,58,44]⟩
def cycle6_5 : CycleData E W := ⟨4,![22,23,19,13,14,26],![8,20,44,30,16,32]⟩
def cycle6_6 : CycleData E W := ⟨3,![27,15,25,30,31],![10,34,32,58,46]⟩
def data6 : PartitionData E W := ⟨7,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4,cycle6_5,cycle6_6]⟩
lemma valid6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel
lemma src_eq6 : src6 = src (unkey (representativeKey 6)) := by decide +kernel
lemma dst_eq6 : dst6 = dst (unkey (representativeKey 6)) := by decide +kernel
lemma certificate6 : Certificate 6 := by
  refine ⟨data6,?_,?_⟩
  · rw [← src_eq6,← dst_eq6]
    exact valid6
  · decide +kernel

def src7 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,30,16,32,34,6,18,44,30,46,8,20,58,44,32,10,34,22,58,46]
def dst7 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,30,16,32,34,4,18,44,30,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle7_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle7_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle7_2 : CycleData E W := ⟨2,![2,21,20,12],![4,6,46,30]⟩
def cycle7_3 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle7_4 : CycleData E W := ⟨2,![10,29,24,18],![18,22,58,44]⟩
def cycle7_5 : CycleData E W := ⟨2,![13,19,25,14],![16,30,44,32]⟩
def cycle7_6 : CycleData E W := ⟨5,![22,23,30,31,27,15,26],![8,20,58,46,10,34,32]⟩
def data7 : PartitionData E W := ⟨7,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4,cycle7_5,cycle7_6]⟩
lemma valid7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel
lemma src_eq7 : src7 = src (unkey (representativeKey 7)) := by decide +kernel
lemma dst_eq7 : dst7 = dst (unkey (representativeKey 7)) := by decide +kernel
lemma certificate7 : Certificate 7 := by
  refine ⟨data7,?_,?_⟩
  · rw [← src_eq7,← dst_eq7]
    exact valid7
  · decide +kernel

def src8 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,16,30,34,6,18,30,44,46,8,20,44,58,32,10,34,22,58,46]
def dst8 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,16,30,34,4,18,30,44,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle8_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle8_1 : CycleData E W := ⟨3,![1,2,17,10,9],![3,4,6,18,22]⟩
def cycle8_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle8_3 : CycleData E W := ⟨3,![5,27,15,18,11],![2,10,34,30,18]⟩
def cycle8_4 : CycleData E W := ⟨3,![12,25,29,28,16],![4,32,58,22,34]⟩
def cycle8_5 : CycleData E W := ⟨4,![22,23,19,14,13,26],![8,20,44,30,16,32]⟩
def cycle8_6 : CycleData E W := ⟨1,![20,30,24],![44,46,58]⟩
def data8 : PartitionData E W := ⟨7,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4,cycle8_5,cycle8_6]⟩
lemma valid8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel
lemma src_eq8 : src8 = src (unkey (representativeKey 8)) := by decide +kernel
lemma dst_eq8 : dst8 = dst (unkey (representativeKey 8)) := by decide +kernel
lemma certificate8 : Certificate 8 := by
  refine ⟨data8,?_,?_⟩
  · rw [← src_eq8,← dst_eq8]
    exact valid8
  · decide +kernel

def src9 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,16,30,34,6,18,44,30,46,8,20,44,58,32,10,34,22,58,46]
def dst9 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,16,30,34,4,18,44,30,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle9_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle9_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle9_2 : CycleData E W := ⟨2,![2,3,26,12],![4,6,8,32]⟩
def cycle9_3 : CycleData E W := ⟨4,![5,4,22,23,18,11],![2,10,8,20,44,18]⟩
def cycle9_4 : CycleData E W := ⟨3,![17,10,29,30,21],![6,18,22,58,46]⟩
def cycle9_5 : CycleData E W := ⟨3,![13,25,24,19,14],![16,32,58,44,30]⟩
def cycle9_6 : CycleData E W := ⟨2,![27,15,20,31],![10,34,30,46]⟩
def data9 : PartitionData E W := ⟨7,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4,cycle9_5,cycle9_6]⟩
lemma valid9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel
lemma src_eq9 : src9 = src (unkey (representativeKey 9)) := by decide +kernel
lemma dst_eq9 : dst9 = dst (unkey (representativeKey 9)) := by decide +kernel
lemma certificate9 : Certificate 9 := by
  refine ⟨data9,?_,?_⟩
  · rw [← src_eq9,← dst_eq9]
    exact valid9
  · decide +kernel

def src10 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,16,30,34,6,18,44,30,46,8,20,58,44,32,10,34,22,58,46]
def dst10 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,16,30,34,4,18,44,30,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle10_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle10_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle10_2 : CycleData E W := ⟨2,![2,3,26,12],![4,6,8,32]⟩
def cycle10_3 : CycleData E W := ⟨5,![5,4,22,23,24,18,11],![2,10,8,20,58,44,18]⟩
def cycle10_4 : CycleData E W := ⟨3,![17,10,29,30,21],![6,18,22,58,46]⟩
def cycle10_5 : CycleData E W := ⟨2,![13,25,19,14],![16,32,44,30]⟩
def cycle10_6 : CycleData E W := ⟨2,![27,15,20,31],![10,34,30,46]⟩
def data10 : PartitionData E W := ⟨7,![cycle10_0,cycle10_1,cycle10_2,cycle10_3,cycle10_4,cycle10_5,cycle10_6]⟩
lemma valid10 : data10.Valid src10 dst10 Finset.univ := by decide +kernel
lemma src_eq10 : src10 = src (unkey (representativeKey 10)) := by decide +kernel
lemma dst_eq10 : dst10 = dst (unkey (representativeKey 10)) := by decide +kernel
lemma certificate10 : Certificate 10 := by
  refine ⟨data10,?_,?_⟩
  · rw [← src_eq10,← dst_eq10]
    exact valid10
  · decide +kernel

def src11 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,30,44,46,8,20,44,58,32,10,34,22,58,46]
def dst11 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,30,44,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle11_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle11_1 : CycleData E W := ⟨3,![1,2,17,10,9],![3,4,6,18,22]⟩
def cycle11_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle11_3 : CycleData E W := ⟨4,![5,27,15,14,18,11],![2,10,34,16,30,18]⟩
def cycle11_4 : CycleData E W := ⟨3,![12,25,29,28,16],![4,32,58,22,34]⟩
def cycle11_5 : CycleData E W := ⟨3,![22,23,19,13,26],![8,20,44,30,32]⟩
def cycle11_6 : CycleData E W := ⟨1,![20,30,24],![44,46,58]⟩
def data11 : PartitionData E W := ⟨7,![cycle11_0,cycle11_1,cycle11_2,cycle11_3,cycle11_4,cycle11_5,cycle11_6]⟩
lemma valid11 : data11.Valid src11 dst11 Finset.univ := by decide +kernel
lemma src_eq11 : src11 = src (unkey (representativeKey 11)) := by decide +kernel
lemma dst_eq11 : dst11 = dst (unkey (representativeKey 11)) := by decide +kernel
lemma certificate11 : Certificate 11 := by
  refine ⟨data11,?_,?_⟩
  · rw [← src_eq11,← dst_eq11]
    exact valid11
  · decide +kernel

def src12 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,30,44,46,8,32,58,20,44,10,34,22,58,46]
def dst12 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,30,44,46,6,32,58,20,44,8,34,22,58,46,10]
def cycle12_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle12_1 : CycleData E W := ⟨3,![1,2,17,10,9],![3,4,6,18,22]⟩
def cycle12_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle12_3 : CycleData E W := ⟨4,![5,27,15,14,18,11],![2,10,34,16,30,18]⟩
def cycle12_4 : CycleData E W := ⟨3,![12,23,29,28,16],![4,32,58,22,34]⟩
def cycle12_5 : CycleData E W := ⟨2,![22,13,19,26],![8,32,30,44]⟩
def cycle12_6 : CycleData E W := ⟨2,![24,30,20,25],![20,58,46,44]⟩
def data12 : PartitionData E W := ⟨7,![cycle12_0,cycle12_1,cycle12_2,cycle12_3,cycle12_4,cycle12_5,cycle12_6]⟩
lemma valid12 : data12.Valid src12 dst12 Finset.univ := by decide +kernel
lemma src_eq12 : src12 = src (unkey (representativeKey 12)) := by decide +kernel
lemma dst_eq12 : dst12 = dst (unkey (representativeKey 12)) := by decide +kernel
lemma certificate12 : Certificate 12 := by
  refine ⟨data12,?_,?_⟩
  · rw [← src_eq12,← dst_eq12]
    exact valid12
  · decide +kernel

def src13 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,30,46,8,20,44,58,32,10,34,22,58,46]
def dst13 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,30,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle13_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle13_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle13_2 : CycleData E W := ⟨2,![2,3,26,12],![4,6,8,32]⟩
def cycle13_3 : CycleData E W := ⟨4,![5,4,22,23,18,11],![2,10,8,20,44,18]⟩
def cycle13_4 : CycleData E W := ⟨3,![17,10,29,30,21],![6,18,22,58,46]⟩
def cycle13_5 : CycleData E W := ⟨2,![13,25,24,19],![30,32,58,44]⟩
def cycle13_6 : CycleData E W := ⟨3,![27,15,14,20,31],![10,34,16,30,46]⟩
def data13 : PartitionData E W := ⟨7,![cycle13_0,cycle13_1,cycle13_2,cycle13_3,cycle13_4,cycle13_5,cycle13_6]⟩
lemma valid13 : data13.Valid src13 dst13 Finset.univ := by decide +kernel
lemma src_eq13 : src13 = src (unkey (representativeKey 13)) := by decide +kernel
lemma dst_eq13 : dst13 = dst (unkey (representativeKey 13)) := by decide +kernel
lemma certificate13 : Certificate 13 := by
  refine ⟨data13,?_,?_⟩
  · rw [← src_eq13,← dst_eq13]
    exact valid13
  · decide +kernel

def src14 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,18,44,30,46,8,32,58,20,44,10,34,22,58,46]
def dst14 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,18,44,30,46,6,32,58,20,44,8,34,22,58,46,10]
def cycle14_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle14_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle14_2 : CycleData E W := ⟨2,![2,3,22,12],![4,6,8,32]⟩
def cycle14_3 : CycleData E W := ⟨3,![5,4,26,18,11],![2,10,8,44,18]⟩
def cycle14_4 : CycleData E W := ⟨3,![17,10,29,30,21],![6,18,22,58,46]⟩
def cycle14_5 : CycleData E W := ⟨3,![24,23,13,19,25],![20,58,32,30,44]⟩
def cycle14_6 : CycleData E W := ⟨3,![27,15,14,20,31],![10,34,16,30,46]⟩
def data14 : PartitionData E W := ⟨7,![cycle14_0,cycle14_1,cycle14_2,cycle14_3,cycle14_4,cycle14_5,cycle14_6]⟩
lemma valid14 : data14.Valid src14 dst14 Finset.univ := by decide +kernel
lemma src_eq14 : src14 = src (unkey (representativeKey 14)) := by decide +kernel
lemma dst_eq14 : dst14 = dst (unkey (representativeKey 14)) := by decide +kernel
lemma certificate14 : Certificate 14 := by
  refine ⟨data14,?_,?_⟩
  · rw [← src_eq14,← dst_eq14]
    exact valid14
  · decide +kernel

def src15 : E → W := ![2,3,4,6,8,10,2,16,20,3,22,18,4,32,30,16,34,6,44,18,30,46,8,32,58,20,44,10,34,22,58,46]
def dst15 : E → W := ![3,4,6,8,10,2,16,20,3,22,18,2,32,30,16,34,4,44,18,30,46,6,32,58,20,44,8,34,22,58,46,10]
def cycle15_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,20,16]⟩
def cycle15_1 : CycleData E W := ⟨2,![1,16,28,9],![3,4,34,22]⟩
def cycle15_2 : CycleData E W := ⟨3,![2,21,20,13,12],![4,6,46,30,32]⟩
def cycle15_3 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle15_4 : CycleData E W := ⟨3,![4,31,30,23,22],![8,10,46,58,32]⟩
def cycle15_5 : CycleData E W := ⟨4,![5,27,15,14,19,11],![2,10,34,16,30,18]⟩
def cycle15_6 : CycleData E W := ⟨3,![10,29,24,25,18],![18,22,58,20,44]⟩
def data15 : PartitionData E W := ⟨7,![cycle15_0,cycle15_1,cycle15_2,cycle15_3,cycle15_4,cycle15_5,cycle15_6]⟩
lemma valid15 : data15.Valid src15 dst15 Finset.univ := by decide +kernel
lemma src_eq15 : src15 = src (unkey (representativeKey 15)) := by decide +kernel
lemma dst_eq15 : dst15 = dst (unkey (representativeKey 15)) := by decide +kernel
lemma certificate15 : Certificate 15 := by
  refine ⟨data15,?_,?_⟩
  · rw [← src_eq15,← dst_eq15]
    exact valid15
  · decide +kernel

def src16 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,16,30,32,34,6,18,30,44,46,8,32,20,58,44,10,34,46,22,58]
def dst16 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,16,30,32,34,4,18,30,44,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle16_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle16_1 : CycleData E W := ⟨4,![1,12,13,18,10,9],![3,4,16,30,18,20]⟩
def cycle16_2 : CycleData E W := ⟨2,![2,21,28,16],![4,6,46,34]⟩
def cycle16_3 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle16_4 : CycleData E W := ⟨2,![22,14,19,26],![8,32,30,44]⟩
def cycle16_5 : CycleData E W := ⟨3,![27,15,23,24,31],![10,34,32,20,58]⟩
def cycle16_6 : CycleData E W := ⟨2,![29,20,25,30],![22,46,44,58]⟩
def data16 : PartitionData E W := ⟨7,![cycle16_0,cycle16_1,cycle16_2,cycle16_3,cycle16_4,cycle16_5,cycle16_6]⟩
lemma valid16 : data16.Valid src16 dst16 Finset.univ := by decide +kernel
lemma src_eq16 : src16 = src (unkey (representativeKey 16)) := by decide +kernel
lemma dst_eq16 : dst16 = dst (unkey (representativeKey 16)) := by decide +kernel
lemma certificate16 : Certificate 16 := by
  refine ⟨data16,?_,?_⟩
  · rw [← src_eq16,← dst_eq16]
    exact valid16
  · decide +kernel

def src17 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,16,30,32,34,6,44,30,18,46,8,32,20,58,44,10,34,46,22,58]
def dst17 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,16,30,32,34,4,44,30,18,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle17_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle17_1 : CycleData E W := ⟨4,![1,12,13,19,10,9],![3,4,16,30,18,20]⟩
def cycle17_2 : CycleData E W := ⟨2,![2,21,28,16],![4,6,46,34]⟩
def cycle17_3 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle17_4 : CycleData E W := ⟨2,![4,27,15,22],![8,10,34,32]⟩
def cycle17_5 : CycleData E W := ⟨4,![5,31,30,29,20,11],![2,10,58,22,46,18]⟩
def cycle17_6 : CycleData E W := ⟨3,![23,14,18,25,24],![20,32,30,44,58]⟩
def data17 : PartitionData E W := ⟨7,![cycle17_0,cycle17_1,cycle17_2,cycle17_3,cycle17_4,cycle17_5,cycle17_6]⟩
lemma valid17 : data17.Valid src17 dst17 Finset.univ := by decide +kernel
lemma src_eq17 : src17 = src (unkey (representativeKey 17)) := by decide +kernel
lemma dst_eq17 : dst17 = dst (unkey (representativeKey 17)) := by decide +kernel
lemma certificate17 : Certificate 17 := by
  refine ⟨data17,?_,?_⟩
  · rw [← src_eq17,← dst_eq17]
    exact valid17
  · decide +kernel

def src18 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,16,30,32,34,6,44,30,18,46,8,32,20,58,44,10,34,58,22,46]
def dst18 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,16,30,32,34,4,44,30,18,46,6,32,20,58,44,8,34,58,22,46,10]
def cycle18_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle18_1 : CycleData E W := ⟨4,![1,12,13,19,10,9],![3,4,16,30,18,20]⟩
def cycle18_2 : CycleData E W := ⟨3,![2,3,4,27,16],![4,6,8,10,34]⟩
def cycle18_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle18_4 : CycleData E W := ⟨2,![22,14,18,26],![8,32,30,44]⟩
def cycle18_5 : CycleData E W := ⟨2,![23,15,28,24],![20,32,34,58]⟩
def cycle18_6 : CycleData E W := ⟨3,![17,25,29,30,21],![6,44,58,22,46]⟩
def data18 : PartitionData E W := ⟨7,![cycle18_0,cycle18_1,cycle18_2,cycle18_3,cycle18_4,cycle18_5,cycle18_6]⟩
lemma valid18 : data18.Valid src18 dst18 Finset.univ := by decide +kernel
lemma src_eq18 : src18 = src (unkey (representativeKey 18)) := by decide +kernel
lemma dst_eq18 : dst18 = dst (unkey (representativeKey 18)) := by decide +kernel
lemma certificate18 : Certificate 18 := by
  refine ⟨data18,?_,?_⟩
  · rw [← src_eq18,← dst_eq18]
    exact valid18
  · decide +kernel

def src19 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,18,30,44,46,8,32,20,58,44,10,34,46,22,58]
def dst19 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,18,30,44,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle19_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle19_1 : CycleData E W := ⟨3,![1,12,18,10,9],![3,4,30,18,20]⟩
def cycle19_2 : CycleData E W := ⟨2,![2,21,28,16],![4,6,46,34]⟩
def cycle19_3 : CycleData E W := ⟨3,![5,4,3,17,11],![2,10,8,6,18]⟩
def cycle19_4 : CycleData E W := ⟨3,![22,14,13,19,26],![8,32,16,30,44]⟩
def cycle19_5 : CycleData E W := ⟨3,![27,15,23,24,31],![10,34,32,20,58]⟩
def cycle19_6 : CycleData E W := ⟨2,![29,20,25,30],![22,46,44,58]⟩
def data19 : PartitionData E W := ⟨7,![cycle19_0,cycle19_1,cycle19_2,cycle19_3,cycle19_4,cycle19_5,cycle19_6]⟩
lemma valid19 : data19.Valid src19 dst19 Finset.univ := by decide +kernel
lemma src_eq19 : src19 = src (unkey (representativeKey 19)) := by decide +kernel
lemma dst_eq19 : dst19 = dst (unkey (representativeKey 19)) := by decide +kernel
lemma certificate19 : Certificate 19 := by
  refine ⟨data19,?_,?_⟩
  · rw [← src_eq19,← dst_eq19]
    exact valid19
  · decide +kernel

def src20 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,32,20,58,44,10,34,46,22,58]
def dst20 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle20_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle20_1 : CycleData E W := ⟨3,![1,12,19,10,9],![3,4,30,18,20]⟩
def cycle20_2 : CycleData E W := ⟨2,![2,21,28,16],![4,6,46,34]⟩
def cycle20_3 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle20_4 : CycleData E W := ⟨2,![4,27,15,22],![8,10,34,32]⟩
def cycle20_5 : CycleData E W := ⟨4,![5,31,30,29,20,11],![2,10,58,22,46,18]⟩
def cycle20_6 : CycleData E W := ⟨4,![13,18,25,24,23,14],![16,30,44,58,20,32]⟩
def data20 : PartitionData E W := ⟨7,![cycle20_0,cycle20_1,cycle20_2,cycle20_3,cycle20_4,cycle20_5,cycle20_6]⟩
lemma valid20 : data20.Valid src20 dst20 Finset.univ := by decide +kernel
lemma src_eq20 : src20 = src (unkey (representativeKey 20)) := by decide +kernel
lemma dst_eq20 : dst20 = dst (unkey (representativeKey 20)) := by decide +kernel
lemma certificate20 : Certificate 20 := by
  refine ⟨data20,?_,?_⟩
  · rw [← src_eq20,← dst_eq20]
    exact valid20
  · decide +kernel

def src21 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,18,30,44,46,8,20,58,44,32,10,34,58,22,46]
def dst21 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,18,30,44,46,6,20,58,44,32,8,34,58,22,46,10]
def cycle21_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle21_1 : CycleData E W := ⟨3,![1,2,17,10,9],![3,4,6,18,20]⟩
def cycle21_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle21_3 : CycleData E W := ⟨3,![5,27,15,18,11],![2,10,34,30,18]⟩
def cycle21_4 : CycleData E W := ⟨4,![12,26,22,23,28,16],![4,32,8,20,58,34]⟩
def cycle21_5 : CycleData E W := ⟨2,![13,25,19,14],![16,32,44,30]⟩
def cycle21_6 : CycleData E W := ⟨2,![29,24,20,30],![22,58,44,46]⟩
def data21 : PartitionData E W := ⟨7,![cycle21_0,cycle21_1,cycle21_2,cycle21_3,cycle21_4,cycle21_5,cycle21_6]⟩
lemma valid21 : data21.Valid src21 dst21 Finset.univ := by decide +kernel
lemma src_eq21 : src21 = src (unkey (representativeKey 21)) := by decide +kernel
lemma dst_eq21 : dst21 = dst (unkey (representativeKey 21)) := by decide +kernel
lemma certificate21 : Certificate 21 := by
  refine ⟨data21,?_,?_⟩
  · rw [← src_eq21,← dst_eq21]
    exact valid21
  · decide +kernel

def src22 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,18,30,44,46,8,32,20,58,44,10,34,58,22,46]
def dst22 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,18,30,44,46,6,32,20,58,44,8,34,58,22,46,10]
def cycle22_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle22_1 : CycleData E W := ⟨3,![1,2,17,10,9],![3,4,6,18,20]⟩
def cycle22_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle22_3 : CycleData E W := ⟨3,![5,27,15,18,11],![2,10,34,30,18]⟩
def cycle22_4 : CycleData E W := ⟨3,![12,23,24,28,16],![4,32,20,58,34]⟩
def cycle22_5 : CycleData E W := ⟨3,![22,13,14,19,26],![8,32,16,30,44]⟩
def cycle22_6 : CycleData E W := ⟨2,![29,25,20,30],![22,58,44,46]⟩
def data22 : PartitionData E W := ⟨7,![cycle22_0,cycle22_1,cycle22_2,cycle22_3,cycle22_4,cycle22_5,cycle22_6]⟩
lemma valid22 : data22.Valid src22 dst22 Finset.univ := by decide +kernel
lemma src_eq22 : src22 = src (unkey (representativeKey 22)) := by decide +kernel
lemma dst_eq22 : dst22 = dst (unkey (representativeKey 22)) := by decide +kernel
lemma certificate22 : Certificate 22 := by
  refine ⟨data22,?_,?_⟩
  · rw [← src_eq22,← dst_eq22]
    exact valid22
  · decide +kernel

def src23 : E → W := ![2,3,4,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,44,30,18,46,8,32,20,58,44,10,34,58,22,46]
def dst23 : E → W := ![3,4,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,44,30,18,46,6,32,20,58,44,8,34,58,22,46,10]
def cycle23_0 : CycleData E W := ⟨2,![0,8,7,6],![2,3,22,16]⟩
def cycle23_1 : CycleData E W := ⟨2,![1,12,23,9],![3,4,32,20]⟩
def cycle23_2 : CycleData E W := ⟨3,![2,3,4,27,16],![4,6,8,10,34]⟩
def cycle23_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle23_4 : CycleData E W := ⟨3,![10,24,28,15,19],![18,20,58,34,30]⟩
def cycle23_5 : CycleData E W := ⟨3,![22,13,14,18,26],![8,32,16,30,44]⟩
def cycle23_6 : CycleData E W := ⟨3,![17,25,29,30,21],![6,44,58,22,46]⟩
def data23 : PartitionData E W := ⟨7,![cycle23_0,cycle23_1,cycle23_2,cycle23_3,cycle23_4,cycle23_5,cycle23_6]⟩
lemma valid23 : data23.Valid src23 dst23 Finset.univ := by decide +kernel
lemma src_eq23 : src23 = src (unkey (representativeKey 23)) := by decide +kernel
lemma dst_eq23 : dst23 = dst (unkey (representativeKey 23)) := by decide +kernel
lemma certificate23 : Certificate 23 := by
  refine ⟨data23,?_,?_⟩
  · rw [← src_eq23,← dst_eq23]
    exact valid23
  · decide +kernel

def src24 : E → W := ![2,4,3,6,8,10,2,16,18,3,22,20,4,30,32,16,34,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst24 : E → W := ![4,3,6,8,10,2,16,18,3,22,20,2,30,32,16,34,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle24_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,20]⟩
def cycle24_1 : CycleData E W := ⟨1,![2,17,8],![3,6,18]⟩
def cycle24_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle24_3 : CycleData E W := ⟨4,![5,4,26,28,15,6],![2,10,8,58,34,16]⟩
def cycle24_4 : CycleData E W := ⟨3,![7,18,24,23,14],![16,18,44,20,32]⟩
def cycle24_5 : CycleData E W := ⟨3,![12,20,31,27,16],![4,30,46,10,34]⟩
def cycle24_6 : CycleData E W := ⟨2,![29,25,19,30],![22,58,44,46]⟩
def data24 : PartitionData E W := ⟨7,![cycle24_0,cycle24_1,cycle24_2,cycle24_3,cycle24_4,cycle24_5,cycle24_6]⟩
lemma valid24 : data24.Valid src24 dst24 Finset.univ := by decide +kernel
lemma src_eq24 : src24 = src (unkey (representativeKey 24)) := by decide +kernel
lemma dst_eq24 : dst24 = dst (unkey (representativeKey 24)) := by decide +kernel
lemma certificate24 : Certificate 24 := by
  refine ⟨data24,?_,?_⟩
  · rw [← src_eq24,← dst_eq24]
    exact valid24
  · decide +kernel

def src25 : E → W := ![2,4,3,6,8,10,2,16,18,3,22,20,4,30,32,16,34,6,18,44,46,30,8,32,20,44,58,10,46,22,34,58]
def dst25 : E → W := ![4,3,6,8,10,2,16,18,3,22,20,2,30,32,16,34,4,18,44,46,30,6,32,20,44,58,8,46,22,34,58,10]
def cycle25_0 : CycleData E W := ⟨3,![0,12,20,27,5],![2,4,30,46,10]⟩
def cycle25_1 : CycleData E W := ⟨2,![1,16,29,9],![3,4,34,22]⟩
def cycle25_2 : CycleData E W := ⟨1,![2,17,8],![3,6,18]⟩
def cycle25_3 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle25_4 : CycleData E W := ⟨1,![4,31,26],![8,10,58]⟩
def cycle25_5 : CycleData E W := ⟨2,![6,14,23,11],![2,16,32,20]⟩
def cycle25_6 : CycleData E W := ⟨3,![7,18,25,30,15],![16,18,44,58,34]⟩
def cycle25_7 : CycleData E W := ⟨2,![10,28,19,24],![20,22,46,44]⟩
def data25 : PartitionData E W := ⟨8,![cycle25_0,cycle25_1,cycle25_2,cycle25_3,cycle25_4,cycle25_5,cycle25_6,cycle25_7]⟩
lemma valid25 : data25.Valid src25 dst25 Finset.univ := by decide +kernel
lemma src_eq25 : src25 = src (unkey (representativeKey 25)) := by decide +kernel
lemma dst_eq25 : dst25 = dst (unkey (representativeKey 25)) := by decide +kernel
lemma certificate25 : Certificate 25 := by
  refine ⟨data25,?_,?_⟩
  · rw [← src_eq25,← dst_eq25]
    exact valid25
  · decide +kernel

def src26 : E → W := ![2,4,3,6,8,10,2,16,18,3,22,20,4,30,34,16,32,6,18,44,46,30,8,20,44,32,58,10,34,58,22,46]
def dst26 : E → W := ![4,3,6,8,10,2,16,18,3,22,20,2,30,34,16,32,4,18,44,46,30,6,20,44,32,58,8,34,58,22,46,10]
def cycle26_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,18,16]⟩
def cycle26_1 : CycleData E W := ⟨3,![2,3,26,29,9],![3,6,8,58,22]⟩
def cycle26_2 : CycleData E W := ⟨2,![5,4,22,11],![2,10,8,20]⟩
def cycle26_3 : CycleData E W := ⟨2,![10,30,19,23],![20,22,46,44]⟩
def cycle26_4 : CycleData E W := ⟨4,![12,21,17,18,24,16],![4,30,6,18,44,32]⟩
def cycle26_5 : CycleData E W := ⟨2,![27,13,20,31],![10,34,30,46]⟩
def cycle26_6 : CycleData E W := ⟨2,![14,28,25,15],![16,34,58,32]⟩
def data26 : PartitionData E W := ⟨7,![cycle26_0,cycle26_1,cycle26_2,cycle26_3,cycle26_4,cycle26_5,cycle26_6]⟩
lemma valid26 : data26.Valid src26 dst26 Finset.univ := by decide +kernel
lemma src_eq26 : src26 = src (unkey (representativeKey 26)) := by decide +kernel
lemma dst_eq26 : dst26 = dst (unkey (representativeKey 26)) := by decide +kernel
lemma certificate26 : Certificate 26 := by
  refine ⟨data26,?_,?_⟩
  · rw [← src_eq26,← dst_eq26]
    exact valid26
  · decide +kernel

def src27 : E → W := ![2,4,3,6,8,10,2,16,18,3,22,20,4,30,34,16,32,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst27 : E → W := ![4,3,6,8,10,2,16,18,3,22,20,2,30,34,16,32,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle27_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,20]⟩
def cycle27_1 : CycleData E W := ⟨1,![2,17,8],![3,6,18]⟩
def cycle27_2 : CycleData E W := ⟨3,![12,21,3,22,16],![4,30,6,8,32]⟩
def cycle27_3 : CycleData E W := ⟨4,![5,4,26,28,14,6],![2,10,8,58,34,16]⟩
def cycle27_4 : CycleData E W := ⟨3,![7,18,24,23,15],![16,18,44,20,32]⟩
def cycle27_5 : CycleData E W := ⟨2,![27,13,20,31],![10,34,30,46]⟩
def cycle27_6 : CycleData E W := ⟨2,![29,25,19,30],![22,58,44,46]⟩
def data27 : PartitionData E W := ⟨7,![cycle27_0,cycle27_1,cycle27_2,cycle27_3,cycle27_4,cycle27_5,cycle27_6]⟩
lemma valid27 : data27.Valid src27 dst27 Finset.univ := by decide +kernel
lemma src_eq27 : src27 = src (unkey (representativeKey 27)) := by decide +kernel
lemma dst_eq27 : dst27 = dst (unkey (representativeKey 27)) := by decide +kernel
lemma certificate27 : Certificate 27 := by
  refine ⟨data27,?_,?_⟩
  · rw [← src_eq27,← dst_eq27]
    exact valid27
  · decide +kernel

def src28 : E → W := ![2,4,3,6,8,10,2,16,18,3,22,20,4,30,34,16,32,6,18,44,46,30,8,32,20,44,58,10,46,22,34,58]
def dst28 : E → W := ![4,3,6,8,10,2,16,18,3,22,20,2,30,34,16,32,4,18,44,46,30,6,32,20,44,58,8,46,22,34,58,10]
def cycle28_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,22,20]⟩
def cycle28_1 : CycleData E W := ⟨1,![2,17,8],![3,6,18]⟩
def cycle28_2 : CycleData E W := ⟨3,![12,21,3,22,16],![4,30,6,8,32]⟩
def cycle28_3 : CycleData E W := ⟨3,![4,27,19,25,26],![8,10,46,44,58]⟩
def cycle28_4 : CycleData E W := ⟨3,![5,31,30,14,6],![2,10,58,34,16]⟩
def cycle28_5 : CycleData E W := ⟨3,![7,18,24,23,15],![16,18,44,20,32]⟩
def cycle28_6 : CycleData E W := ⟨2,![28,20,13,29],![22,46,30,34]⟩
def data28 : PartitionData E W := ⟨7,![cycle28_0,cycle28_1,cycle28_2,cycle28_3,cycle28_4,cycle28_5,cycle28_6]⟩
lemma valid28 : data28.Valid src28 dst28 Finset.univ := by decide +kernel
lemma src_eq28 : src28 = src (unkey (representativeKey 28)) := by decide +kernel
lemma dst_eq28 : dst28 = dst (unkey (representativeKey 28)) := by decide +kernel
lemma certificate28 : Certificate 28 := by
  refine ⟨data28,?_,?_⟩
  · rw [← src_eq28,← dst_eq28]
    exact valid28
  · decide +kernel

def src29 : E → W := ![2,4,3,6,8,10,2,16,18,20,3,22,4,30,34,16,32,6,18,44,46,30,8,20,58,32,44,10,34,58,22,46]
def dst29 : E → W := ![4,3,6,8,10,2,16,18,20,3,22,2,30,34,16,32,4,18,44,46,30,6,20,58,32,44,8,34,58,22,46,10]
def cycle29_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,22]⟩
def cycle29_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,20]⟩
def cycle29_2 : CycleData E W := ⟨5,![12,21,3,22,23,24,16],![4,30,6,8,20,58,32]⟩
def cycle29_3 : CycleData E W := ⟨2,![4,31,19,26],![8,10,46,44]⟩
def cycle29_4 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle29_5 : CycleData E W := ⟨2,![7,18,25,15],![16,18,44,32]⟩
def cycle29_6 : CycleData E W := ⟨3,![29,28,13,20,30],![22,58,34,30,46]⟩
def data29 : PartitionData E W := ⟨7,![cycle29_0,cycle29_1,cycle29_2,cycle29_3,cycle29_4,cycle29_5,cycle29_6]⟩
lemma valid29 : data29.Valid src29 dst29 Finset.univ := by decide +kernel
lemma src_eq29 : src29 = src (unkey (representativeKey 29)) := by decide +kernel
lemma dst_eq29 : dst29 = dst (unkey (representativeKey 29)) := by decide +kernel
lemma certificate29 : Certificate 29 := by
  refine ⟨data29,?_,?_⟩
  · rw [← src_eq29,← dst_eq29]
    exact valid29
  · decide +kernel

def src30 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,16,34,32,30,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst30 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,16,34,32,30,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle30_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle30_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle30_2 : CycleData E W := ⟨2,![3,22,15,21],![6,8,32,30]⟩
def cycle30_3 : CycleData E W := ⟨2,![4,27,28,26],![8,10,34,58]⟩
def cycle30_4 : CycleData E W := ⟨4,![5,31,20,16,12,6],![2,10,46,30,4,16]⟩
def cycle30_5 : CycleData E W := ⟨4,![7,18,24,23,14,13],![16,18,44,20,32,34]⟩
def cycle30_6 : CycleData E W := ⟨2,![29,25,19,30],![22,58,44,46]⟩
def data30 : PartitionData E W := ⟨7,![cycle30_0,cycle30_1,cycle30_2,cycle30_3,cycle30_4,cycle30_5,cycle30_6]⟩
lemma valid30 : data30.Valid src30 dst30 Finset.univ := by decide +kernel
lemma src_eq30 : src30 = src (unkey (representativeKey 30)) := by decide +kernel
lemma dst_eq30 : dst30 = dst (unkey (representativeKey 30)) := by decide +kernel
lemma certificate30 : Certificate 30 := by
  refine ⟨data30,?_,?_⟩
  · rw [← src_eq30,← dst_eq30]
    exact valid30
  · decide +kernel

def src31 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,32,34,6,18,44,46,30,8,32,20,58,44,10,46,22,34,58]
def dst31 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,32,34,4,18,44,46,30,6,32,20,58,44,8,46,22,34,58,10]
def cycle31_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle31_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle31_2 : CycleData E W := ⟨4,![5,4,3,21,13,6],![2,10,8,6,30,16]⟩
def cycle31_3 : CycleData E W := ⟨3,![22,14,7,18,26],![8,32,16,18,44]⟩
def cycle31_4 : CycleData E W := ⟨3,![12,20,28,29,16],![4,30,46,22,34]⟩
def cycle31_5 : CycleData E W := ⟨2,![23,15,30,24],![20,32,34,58]⟩
def cycle31_6 : CycleData E W := ⟨2,![27,19,25,31],![10,46,44,58]⟩
def data31 : PartitionData E W := ⟨7,![cycle31_0,cycle31_1,cycle31_2,cycle31_3,cycle31_4,cycle31_5,cycle31_6]⟩
lemma valid31 : data31.Valid src31 dst31 Finset.univ := by decide +kernel
lemma src_eq31 : src31 = src (unkey (representativeKey 31)) := by decide +kernel
lemma dst_eq31 : dst31 = dst (unkey (representativeKey 31)) := by decide +kernel
lemma certificate31 : Certificate 31 := by
  refine ⟨data31,?_,?_⟩
  · rw [← src_eq31,← dst_eq31]
    exact valid31
  · decide +kernel

def src32 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,32,34,6,18,44,46,30,8,32,44,20,58,10,22,34,58,46]
def dst32 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,32,34,4,18,44,46,30,6,32,44,20,58,8,22,34,58,46,10]
def cycle32_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle32_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle32_2 : CycleData E W := ⟨4,![5,4,3,21,13,6],![2,10,8,6,30,16]⟩
def cycle32_3 : CycleData E W := ⟨2,![7,18,23,14],![16,18,44,32]⟩
def cycle32_4 : CycleData E W := ⟨4,![12,20,31,27,28,16],![4,30,46,10,22,34]⟩
def cycle32_5 : CycleData E W := ⟨2,![22,15,29,26],![8,32,34,58]⟩
def cycle32_6 : CycleData E W := ⟨2,![24,19,30,25],![20,44,46,58]⟩
def data32 : PartitionData E W := ⟨7,![cycle32_0,cycle32_1,cycle32_2,cycle32_3,cycle32_4,cycle32_5,cycle32_6]⟩
lemma valid32 : data32.Valid src32 dst32 Finset.univ := by decide +kernel
lemma src_eq32 : src32 = src (unkey (representativeKey 32)) := by decide +kernel
lemma dst_eq32 : dst32 = dst (unkey (representativeKey 32)) := by decide +kernel
lemma certificate32 : Certificate 32 := by
  refine ⟨data32,?_,?_⟩
  · rw [← src_eq32,← dst_eq32]
    exact valid32
  · decide +kernel

def src33 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,32,34,6,18,44,46,30,8,32,44,20,58,10,34,22,58,46]
def dst33 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,32,34,4,18,44,46,30,6,32,44,20,58,8,34,22,58,46,10]
def cycle33_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle33_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle33_2 : CycleData E W := ⟨4,![5,4,3,21,13,6],![2,10,8,6,30,16]⟩
def cycle33_3 : CycleData E W := ⟨2,![7,18,23,14],![16,18,44,32]⟩
def cycle33_4 : CycleData E W := ⟨3,![12,20,31,27,16],![4,30,46,10,34]⟩
def cycle33_5 : CycleData E W := ⟨3,![22,15,28,29,26],![8,32,34,22,58]⟩
def cycle33_6 : CycleData E W := ⟨2,![24,19,30,25],![20,44,46,58]⟩
def data33 : PartitionData E W := ⟨7,![cycle33_0,cycle33_1,cycle33_2,cycle33_3,cycle33_4,cycle33_5,cycle33_6]⟩
lemma valid33 : data33.Valid src33 dst33 Finset.univ := by decide +kernel
lemma src_eq33 : src33 = src (unkey (representativeKey 33)) := by decide +kernel
lemma dst_eq33 : dst33 = dst (unkey (representativeKey 33)) := by decide +kernel
lemma certificate33 : Certificate 33 := by
  refine ⟨data33,?_,?_⟩
  · rw [← src_eq33,← dst_eq33]
    exact valid33
  · decide +kernel

def src34 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,32,34,6,18,44,46,30,8,32,44,20,58,10,46,22,34,58]
def dst34 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,32,34,4,18,44,46,30,6,32,44,20,58,8,46,22,34,58,10]
def cycle34_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle34_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle34_2 : CycleData E W := ⟨4,![5,4,3,21,13,6],![2,10,8,6,30,16]⟩
def cycle34_3 : CycleData E W := ⟨2,![7,18,23,14],![16,18,44,32]⟩
def cycle34_4 : CycleData E W := ⟨3,![12,20,28,29,16],![4,30,46,22,34]⟩
def cycle34_5 : CycleData E W := ⟨2,![22,15,30,26],![8,32,34,58]⟩
def cycle34_6 : CycleData E W := ⟨3,![27,19,24,25,31],![10,46,44,20,58]⟩
def data34 : PartitionData E W := ⟨7,![cycle34_0,cycle34_1,cycle34_2,cycle34_3,cycle34_4,cycle34_5,cycle34_6]⟩
lemma valid34 : data34.Valid src34 dst34 Finset.univ := by decide +kernel
lemma src_eq34 : src34 = src (unkey (representativeKey 34)) := by decide +kernel
lemma dst_eq34 : dst34 = dst (unkey (representativeKey 34)) := by decide +kernel
lemma certificate34 : Certificate 34 := by
  refine ⟨data34,?_,?_⟩
  · rw [← src_eq34,← dst_eq34]
    exact valid34
  · decide +kernel

def src35 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,32,34,6,18,44,46,30,8,32,44,20,58,10,46,34,22,58]
def dst35 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,32,34,4,18,44,46,30,6,32,44,20,58,8,46,34,22,58,10]
def cycle35_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle35_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle35_2 : CycleData E W := ⟨4,![5,4,3,21,13,6],![2,10,8,6,30,16]⟩
def cycle35_3 : CycleData E W := ⟨2,![7,18,23,14],![16,18,44,32]⟩
def cycle35_4 : CycleData E W := ⟨2,![12,20,28,16],![4,30,46,34]⟩
def cycle35_5 : CycleData E W := ⟨3,![22,15,29,30,26],![8,32,34,22,58]⟩
def cycle35_6 : CycleData E W := ⟨3,![27,19,24,25,31],![10,46,44,20,58]⟩
def data35 : PartitionData E W := ⟨7,![cycle35_0,cycle35_1,cycle35_2,cycle35_3,cycle35_4,cycle35_5,cycle35_6]⟩
lemma valid35 : data35.Valid src35 dst35 Finset.univ := by decide +kernel
lemma src_eq35 : src35 = src (unkey (representativeKey 35)) := by decide +kernel
lemma dst_eq35 : dst35 = dst (unkey (representativeKey 35)) := by decide +kernel
lemma certificate35 : Certificate 35 := by
  refine ⟨data35,?_,?_⟩
  · rw [← src_eq35,← dst_eq35]
    exact valid35
  · decide +kernel

def src36 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,34,32,6,18,44,46,30,8,32,20,44,58,10,22,58,34,46]
def dst36 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,34,32,4,18,44,46,30,6,32,20,44,58,8,22,58,34,46,10]
def cycle36_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle36_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle36_2 : CycleData E W := ⟨3,![12,21,3,22,16],![4,30,6,8,32]⟩
def cycle36_3 : CycleData E W := ⟨2,![4,27,28,26],![8,10,22,58]⟩
def cycle36_4 : CycleData E W := ⟨4,![5,31,19,18,7,6],![2,10,46,44,18,16]⟩
def cycle36_5 : CycleData E W := ⟨2,![13,20,30,14],![16,30,46,34]⟩
def cycle36_6 : CycleData E W := ⟨3,![23,15,29,25,24],![20,32,34,58,44]⟩
def data36 : PartitionData E W := ⟨7,![cycle36_0,cycle36_1,cycle36_2,cycle36_3,cycle36_4,cycle36_5,cycle36_6]⟩
lemma valid36 : data36.Valid src36 dst36 Finset.univ := by decide +kernel
lemma src_eq36 : src36 = src (unkey (representativeKey 36)) := by decide +kernel
lemma dst_eq36 : dst36 = dst (unkey (representativeKey 36)) := by decide +kernel
lemma certificate36 : Certificate 36 := by
  refine ⟨data36,?_,?_⟩
  · rw [← src_eq36,← dst_eq36]
    exact valid36
  · decide +kernel

def src37 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,34,32,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst37 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,34,32,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle37_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle37_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle37_2 : CycleData E W := ⟨3,![12,21,3,22,16],![4,30,6,8,32]⟩
def cycle37_3 : CycleData E W := ⟨2,![4,27,28,26],![8,10,34,58]⟩
def cycle37_4 : CycleData E W := ⟨3,![5,31,20,13,6],![2,10,46,30,16]⟩
def cycle37_5 : CycleData E W := ⟨4,![7,18,24,23,15,14],![16,18,44,20,32,34]⟩
def cycle37_6 : CycleData E W := ⟨2,![29,25,19,30],![22,58,44,46]⟩
def data37 : PartitionData E W := ⟨7,![cycle37_0,cycle37_1,cycle37_2,cycle37_3,cycle37_4,cycle37_5,cycle37_6]⟩
lemma valid37 : data37.Valid src37 dst37 Finset.univ := by decide +kernel
lemma src_eq37 : src37 = src (unkey (representativeKey 37)) := by decide +kernel
lemma dst_eq37 : dst37 = dst (unkey (representativeKey 37)) := by decide +kernel
lemma certificate37 : Certificate 37 := by
  refine ⟨data37,?_,?_⟩
  · rw [← src_eq37,← dst_eq37]
    exact valid37
  · decide +kernel

def src38 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,34,32,6,18,44,46,30,8,32,44,20,58,10,22,58,34,46]
def dst38 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,34,32,4,18,44,46,30,6,32,44,20,58,8,22,58,34,46,10]
def cycle38_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle38_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle38_2 : CycleData E W := ⟨3,![12,21,3,22,16],![4,30,6,8,32]⟩
def cycle38_3 : CycleData E W := ⟨2,![4,27,28,26],![8,10,22,58]⟩
def cycle38_4 : CycleData E W := ⟨4,![5,31,19,18,7,6],![2,10,46,44,18,16]⟩
def cycle38_5 : CycleData E W := ⟨2,![13,20,30,14],![16,30,46,34]⟩
def cycle38_6 : CycleData E W := ⟨3,![24,23,15,29,25],![20,44,32,34,58]⟩
def data38 : PartitionData E W := ⟨7,![cycle38_0,cycle38_1,cycle38_2,cycle38_3,cycle38_4,cycle38_5,cycle38_6]⟩
lemma valid38 : data38.Valid src38 dst38 Finset.univ := by decide +kernel
lemma src_eq38 : src38 = src (unkey (representativeKey 38)) := by decide +kernel
lemma dst_eq38 : dst38 = dst (unkey (representativeKey 38)) := by decide +kernel
lemma certificate38 : Certificate 38 := by
  refine ⟨data38,?_,?_⟩
  · rw [← src_eq38,← dst_eq38]
    exact valid38
  · decide +kernel

def src39 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,16,34,32,6,18,44,46,30,8,32,44,20,58,10,34,58,22,46]
def dst39 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,16,34,32,4,18,44,46,30,6,32,44,20,58,8,34,58,22,46,10]
def cycle39_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle39_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle39_2 : CycleData E W := ⟨3,![12,21,3,22,16],![4,30,6,8,32]⟩
def cycle39_3 : CycleData E W := ⟨2,![4,27,28,26],![8,10,34,58]⟩
def cycle39_4 : CycleData E W := ⟨3,![5,31,20,13,6],![2,10,46,30,16]⟩
def cycle39_5 : CycleData E W := ⟨3,![7,18,23,15,14],![16,18,44,32,34]⟩
def cycle39_6 : CycleData E W := ⟨3,![24,19,30,29,25],![20,44,46,22,58]⟩
def data39 : PartitionData E W := ⟨7,![cycle39_0,cycle39_1,cycle39_2,cycle39_3,cycle39_4,cycle39_5,cycle39_6]⟩
lemma valid39 : data39.Valid src39 dst39 Finset.univ := by decide +kernel
lemma src_eq39 : src39 = src (unkey (representativeKey 39)) := by decide +kernel
lemma dst_eq39 : dst39 = dst (unkey (representativeKey 39)) := by decide +kernel
lemma certificate39 : Certificate 39 := by
  refine ⟨data39,?_,?_⟩
  · rw [← src_eq39,← dst_eq39]
    exact valid39
  · decide +kernel

def src40 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,20,44,58,10,22,34,58,46]
def dst40 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,20,44,58,8,22,34,58,46,10]
def cycle40_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle40_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle40_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle40_3 : CycleData E W := ⟨4,![5,4,26,29,15,6],![2,10,8,58,34,16]⟩
def cycle40_4 : CycleData E W := ⟨3,![7,18,24,23,14],![16,18,44,20,32]⟩
def cycle40_5 : CycleData E W := ⟨4,![12,20,31,27,28,16],![4,30,46,10,22,34]⟩
def cycle40_6 : CycleData E W := ⟨1,![19,30,25],![44,46,58]⟩
def data40 : PartitionData E W := ⟨7,![cycle40_0,cycle40_1,cycle40_2,cycle40_3,cycle40_4,cycle40_5,cycle40_6]⟩
lemma valid40 : data40.Valid src40 dst40 Finset.univ := by decide +kernel
lemma src_eq40 : src40 = src (unkey (representativeKey 40)) := by decide +kernel
lemma dst_eq40 : dst40 = dst (unkey (representativeKey 40)) := by decide +kernel
lemma certificate40 : Certificate 40 := by
  refine ⟨data40,?_,?_⟩
  · rw [← src_eq40,← dst_eq40]
    exact valid40
  · decide +kernel

def src41 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,20,44,58,10,22,58,34,46]
def dst41 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,20,44,58,8,22,58,34,46,10]
def cycle41_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle41_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle41_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle41_3 : CycleData E W := ⟨2,![4,27,28,26],![8,10,22,58]⟩
def cycle41_4 : CycleData E W := ⟨4,![5,31,19,18,7,6],![2,10,46,44,18,16]⟩
def cycle41_5 : CycleData E W := ⟨2,![12,20,30,16],![4,30,46,34]⟩
def cycle41_6 : CycleData E W := ⟨4,![14,23,24,25,29,15],![16,32,20,44,58,34]⟩
def data41 : PartitionData E W := ⟨7,![cycle41_0,cycle41_1,cycle41_2,cycle41_3,cycle41_4,cycle41_5,cycle41_6]⟩
lemma valid41 : data41.Valid src41 dst41 Finset.univ := by decide +kernel
lemma src_eq41 : src41 = src (unkey (representativeKey 41)) := by decide +kernel
lemma dst_eq41 : dst41 = dst (unkey (representativeKey 41)) := by decide +kernel
lemma certificate41 : Certificate 41 := by
  refine ⟨data41,?_,?_⟩
  · rw [← src_eq41,← dst_eq41]
    exact valid41
  · decide +kernel

def src42 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst42 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle42_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle42_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle42_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle42_3 : CycleData E W := ⟨4,![5,4,26,28,15,6],![2,10,8,58,34,16]⟩
def cycle42_4 : CycleData E W := ⟨3,![7,18,24,23,14],![16,18,44,20,32]⟩
def cycle42_5 : CycleData E W := ⟨3,![12,20,31,27,16],![4,30,46,10,34]⟩
def cycle42_6 : CycleData E W := ⟨2,![29,25,19,30],![22,58,44,46]⟩
def data42 : PartitionData E W := ⟨7,![cycle42_0,cycle42_1,cycle42_2,cycle42_3,cycle42_4,cycle42_5,cycle42_6]⟩
lemma valid42 : data42.Valid src42 dst42 Finset.univ := by decide +kernel
lemma src_eq42 : src42 = src (unkey (representativeKey 42)) := by decide +kernel
lemma dst_eq42 : dst42 = dst (unkey (representativeKey 42)) := by decide +kernel
lemma certificate42 : Certificate 42 := by
  refine ⟨data42,?_,?_⟩
  · rw [← src_eq42,← dst_eq42]
    exact valid42
  · decide +kernel

def src43 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,20,44,58,10,46,22,34,58]
def dst43 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,20,44,58,8,46,22,34,58,10]
def cycle43_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle43_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle43_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle43_3 : CycleData E W := ⟨3,![4,27,19,25,26],![8,10,46,44,58]⟩
def cycle43_4 : CycleData E W := ⟨3,![5,31,30,15,6],![2,10,58,34,16]⟩
def cycle43_5 : CycleData E W := ⟨3,![7,18,24,23,14],![16,18,44,20,32]⟩
def cycle43_6 : CycleData E W := ⟨3,![12,20,28,29,16],![4,30,46,22,34]⟩
def data43 : PartitionData E W := ⟨7,![cycle43_0,cycle43_1,cycle43_2,cycle43_3,cycle43_4,cycle43_5,cycle43_6]⟩
lemma valid43 : data43.Valid src43 dst43 Finset.univ := by decide +kernel
lemma src_eq43 : src43 = src (unkey (representativeKey 43)) := by decide +kernel
lemma dst_eq43 : dst43 = dst (unkey (representativeKey 43)) := by decide +kernel
lemma certificate43 : Certificate 43 := by
  refine ⟨data43,?_,?_⟩
  · rw [← src_eq43,← dst_eq43]
    exact valid43
  · decide +kernel

def src44 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,20,58,44,10,22,58,34,46]
def dst44 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,20,58,44,8,22,58,34,46,10]
def cycle44_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle44_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle44_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle44_3 : CycleData E W := ⟨4,![5,4,26,18,7,6],![2,10,8,44,18,16]⟩
def cycle44_4 : CycleData E W := ⟨2,![12,20,30,16],![4,30,46,34]⟩
def cycle44_5 : CycleData E W := ⟨3,![14,23,24,29,15],![16,32,20,58,34]⟩
def cycle44_6 : CycleData E W := ⟨3,![27,28,25,19,31],![10,22,58,44,46]⟩
def data44 : PartitionData E W := ⟨7,![cycle44_0,cycle44_1,cycle44_2,cycle44_3,cycle44_4,cycle44_5,cycle44_6]⟩
lemma valid44 : data44.Valid src44 dst44 Finset.univ := by decide +kernel
lemma src_eq44 : src44 = src (unkey (representativeKey 44)) := by decide +kernel
lemma dst_eq44 : dst44 = dst (unkey (representativeKey 44)) := by decide +kernel
lemma certificate44 : Certificate 44 := by
  refine ⟨data44,?_,?_⟩
  · rw [← src_eq44,← dst_eq44]
    exact valid44
  · decide +kernel

def src45 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,20,58,44,10,46,22,34,58]
def dst45 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,20,58,44,8,46,22,34,58,10]
def cycle45_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle45_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle45_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle45_3 : CycleData E W := ⟨4,![5,4,26,18,7,6],![2,10,8,44,18,16]⟩
def cycle45_4 : CycleData E W := ⟨3,![12,20,28,29,16],![4,30,46,22,34]⟩
def cycle45_5 : CycleData E W := ⟨3,![14,23,24,30,15],![16,32,20,58,34]⟩
def cycle45_6 : CycleData E W := ⟨2,![27,19,25,31],![10,46,44,58]⟩
def data45 : PartitionData E W := ⟨7,![cycle45_0,cycle45_1,cycle45_2,cycle45_3,cycle45_4,cycle45_5,cycle45_6]⟩
lemma valid45 : data45.Valid src45 dst45 Finset.univ := by decide +kernel
lemma src_eq45 : src45 = src (unkey (representativeKey 45)) := by decide +kernel
lemma dst_eq45 : dst45 = dst (unkey (representativeKey 45)) := by decide +kernel
lemma certificate45 : Certificate 45 := by
  refine ⟨data45,?_,?_⟩
  · rw [← src_eq45,← dst_eq45]
    exact valid45
  · decide +kernel

def src46 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,58,20,44,10,22,58,34,46]
def dst46 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,58,20,44,8,22,58,34,46,10]
def cycle46_0 : CycleData E W := ⟨4,![0,1,9,8,7,6],![2,4,3,22,18,16]⟩
def cycle46_1 : CycleData E W := ⟨3,![2,17,18,25,10],![3,6,18,44,20]⟩
def cycle46_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle46_3 : CycleData E W := ⟨2,![4,31,19,26],![8,10,46,44]⟩
def cycle46_4 : CycleData E W := ⟨3,![5,27,28,24,11],![2,10,22,58,20]⟩
def cycle46_5 : CycleData E W := ⟨2,![12,20,30,16],![4,30,46,34]⟩
def cycle46_6 : CycleData E W := ⟨2,![14,23,29,15],![16,32,58,34]⟩
def data46 : PartitionData E W := ⟨7,![cycle46_0,cycle46_1,cycle46_2,cycle46_3,cycle46_4,cycle46_5,cycle46_6]⟩
lemma valid46 : data46.Valid src46 dst46 Finset.univ := by decide +kernel
lemma src_eq46 : src46 = src (unkey (representativeKey 46)) := by decide +kernel
lemma dst_eq46 : dst46 = dst (unkey (representativeKey 46)) := by decide +kernel
lemma certificate46 : Certificate 46 := by
  refine ⟨data46,?_,?_⟩
  · rw [← src_eq46,← dst_eq46]
    exact valid46
  · decide +kernel

def src47 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,58,20,44,10,46,22,34,58]
def dst47 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,58,20,44,8,46,22,34,58,10]
def cycle47_0 : CycleData E W := ⟨4,![0,1,9,8,7,6],![2,4,3,22,18,16]⟩
def cycle47_1 : CycleData E W := ⟨3,![2,17,18,25,10],![3,6,18,44,20]⟩
def cycle47_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle47_3 : CycleData E W := ⟨2,![4,27,19,26],![8,10,46,44]⟩
def cycle47_4 : CycleData E W := ⟨2,![5,31,24,11],![2,10,58,20]⟩
def cycle47_5 : CycleData E W := ⟨3,![12,20,28,29,16],![4,30,46,22,34]⟩
def cycle47_6 : CycleData E W := ⟨2,![14,23,30,15],![16,32,58,34]⟩
def data47 : PartitionData E W := ⟨7,![cycle47_0,cycle47_1,cycle47_2,cycle47_3,cycle47_4,cycle47_5,cycle47_6]⟩
lemma valid47 : data47.Valid src47 dst47 Finset.univ := by decide +kernel
lemma src_eq47 : src47 = src (unkey (representativeKey 47)) := by decide +kernel
lemma dst_eq47 : dst47 = dst (unkey (representativeKey 47)) := by decide +kernel
lemma certificate47 : Certificate 47 := by
  refine ⟨data47,?_,?_⟩
  · rw [← src_eq47,← dst_eq47]
    exact valid47
  · decide +kernel

def src48 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,32,16,34,6,18,44,46,30,8,32,58,20,44,10,46,34,22,58]
def dst48 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,32,16,34,4,18,44,46,30,6,32,58,20,44,8,46,34,22,58,10]
def cycle48_0 : CycleData E W := ⟨4,![0,1,9,8,7,6],![2,4,3,22,18,16]⟩
def cycle48_1 : CycleData E W := ⟨3,![2,17,18,25,10],![3,6,18,44,20]⟩
def cycle48_2 : CycleData E W := ⟨2,![3,22,13,21],![6,8,32,30]⟩
def cycle48_3 : CycleData E W := ⟨2,![4,27,19,26],![8,10,46,44]⟩
def cycle48_4 : CycleData E W := ⟨2,![5,31,24,11],![2,10,58,20]⟩
def cycle48_5 : CycleData E W := ⟨2,![12,20,28,16],![4,30,46,34]⟩
def cycle48_6 : CycleData E W := ⟨3,![14,23,30,29,15],![16,32,58,22,34]⟩
def data48 : PartitionData E W := ⟨7,![cycle48_0,cycle48_1,cycle48_2,cycle48_3,cycle48_4,cycle48_5,cycle48_6]⟩
lemma valid48 : data48.Valid src48 dst48 Finset.univ := by decide +kernel
lemma src_eq48 : src48 = src (unkey (representativeKey 48)) := by decide +kernel
lemma dst_eq48 : dst48 = dst (unkey (representativeKey 48)) := by decide +kernel
lemma certificate48 : Certificate 48 := by
  refine ⟨data48,?_,?_⟩
  · rw [← src_eq48,← dst_eq48]
    exact valid48
  · decide +kernel

def src49 : E → W := ![2,4,3,6,8,10,2,16,18,22,3,20,4,30,34,16,32,6,18,44,46,30,8,20,44,32,58,10,34,58,22,46]
def dst49 : E → W := ![4,3,6,8,10,2,16,18,22,3,20,2,30,34,16,32,4,18,44,46,30,6,20,44,32,58,8,34,58,22,46,10]
def cycle49_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,20]⟩
def cycle49_1 : CycleData E W := ⟨2,![2,17,8,9],![3,6,18,22]⟩
def cycle49_2 : CycleData E W := ⟨4,![3,22,23,19,20,21],![6,8,20,44,46,30]⟩
def cycle49_3 : CycleData E W := ⟨3,![4,31,30,29,26],![8,10,46,22,58]⟩
def cycle49_4 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle49_5 : CycleData E W := ⟨2,![7,18,24,15],![16,18,44,32]⟩
def cycle49_6 : CycleData E W := ⟨3,![12,13,28,25,16],![4,30,34,58,32]⟩
def data49 : PartitionData E W := ⟨7,![cycle49_0,cycle49_1,cycle49_2,cycle49_3,cycle49_4,cycle49_5,cycle49_6]⟩
lemma valid49 : data49.Valid src49 dst49 Finset.univ := by decide +kernel
lemma src_eq49 : src49 = src (unkey (representativeKey 49)) := by decide +kernel
lemma dst_eq49 : dst49 = dst (unkey (representativeKey 49)) := by decide +kernel
lemma certificate49 : Certificate 49 := by
  refine ⟨data49,?_,?_⟩
  · rw [← src_eq49,← dst_eq49]
    exact valid49
  · decide +kernel
#print axioms certificate49
end Erdos184Work.SixRepresentativeCertificates1

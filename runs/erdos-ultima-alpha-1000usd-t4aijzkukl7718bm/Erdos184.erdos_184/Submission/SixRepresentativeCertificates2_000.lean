import Submission.SixRepresentativeCertificates2Base
namespace Erdos184Work.SixRepresentativeCertificates2
open PureSixRowModel2 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src0 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,30,16,31,34,6,30,46,18,44,31,8,20,44,58,32,10,46,34,22,58]
def dst0 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,30,16,31,34,4,30,46,18,44,31,6,20,44,58,32,8,46,34,22,58,10]
def cycle0_0 : CycleData E W := ⟨4,![0,1,9,8,7,6],![2,4,3,22,20,16]⟩
def cycle0_1 : CycleData E W := ⟨3,![2,23,22,21,10],![3,6,31,44,18]⟩
def cycle0_2 : CycleData E W := ⟨2,![3,28,13,18],![6,8,32,30]⟩
def cycle0_3 : CycleData E W := ⟨3,![4,33,26,25,24],![8,10,58,44,20]⟩
def cycle0_4 : CycleData E W := ⟨2,![5,29,20,11],![2,10,46,18]⟩
def cycle0_5 : CycleData E W := ⟨3,![12,27,32,31,17],![4,32,58,22,34]⟩
def cycle0_6 : CycleData E W := ⟨3,![14,19,30,16,15],![16,30,46,34,31]⟩
def data0 : PartitionData E W := ⟨7,![cycle0_0,cycle0_1,cycle0_2,cycle0_3,cycle0_4,cycle0_5,cycle0_6]⟩
lemma valid0 : data0.Valid src0 dst0 Finset.univ := by decide +kernel
lemma src_eq0 : src0 = src (unkey (representativeKey 0)) := by decide +kernel
lemma dst_eq0 : dst0 = dst (unkey (representativeKey 0)) := by decide +kernel
lemma certificate0 : Certificate 0 := by
  refine ⟨data0,?_,?_⟩
  · rw [← src_eq0,← dst_eq0]
    exact valid0
  · decide +kernel

def src1 : E → W := ![2,4,3,8,6,10,2,18,3,22,16,20,4,32,30,16,31,34,6,30,46,18,44,31,8,20,44,58,32,10,46,34,22,58]
def dst1 : E → W := ![4,3,8,6,10,2,18,3,22,16,20,2,32,30,16,31,34,4,30,46,18,44,31,6,20,44,58,32,8,46,34,22,58,10]
def cycle1_0 : CycleData E W := ⟨2,![0,1,7,6],![2,4,3,18]⟩
def cycle1_1 : CycleData E W := ⟨4,![2,3,23,15,9,8],![3,8,6,31,16,22]⟩
def cycle1_2 : CycleData E W := ⟨2,![4,29,19,18],![6,10,46,30]⟩
def cycle1_3 : CycleData E W := ⟨3,![5,33,26,25,11],![2,10,58,44,20]⟩
def cycle1_4 : CycleData E W := ⟨3,![24,10,14,13,28],![8,20,16,30,32]⟩
def cycle1_5 : CycleData E W := ⟨3,![12,27,32,31,17],![4,32,58,22,34]⟩
def cycle1_6 : CycleData E W := ⟨3,![20,30,16,22,21],![18,46,34,31,44]⟩
def data1 : PartitionData E W := ⟨7,![cycle1_0,cycle1_1,cycle1_2,cycle1_3,cycle1_4,cycle1_5,cycle1_6]⟩
lemma valid1 : data1.Valid src1 dst1 Finset.univ := by decide +kernel
lemma src_eq1 : src1 = src (unkey (representativeKey 1)) := by decide +kernel
lemma dst_eq1 : dst1 = dst (unkey (representativeKey 1)) := by decide +kernel
lemma certificate1 : Certificate 1 := by
  refine ⟨data1,?_,?_⟩
  · rw [← src_eq1,← dst_eq1]
    exact valid1
  · decide +kernel

def src2 : E → W := ![2,4,8,3,6,10,2,16,22,3,18,20,4,30,16,32,31,34,6,31,18,46,30,44,8,20,32,58,44,10,46,34,22,58]
def dst2 : E → W := ![4,8,3,6,10,2,16,22,3,18,20,2,30,16,32,31,34,4,31,18,46,30,44,6,20,32,58,44,8,46,34,22,58,10]
def cycle2_0 : CycleData E W := ⟨4,![0,1,2,8,7,6],![2,4,8,3,22,16]⟩
def cycle2_1 : CycleData E W := ⟨2,![3,18,19,9],![3,6,31,18]⟩
def cycle2_2 : CycleData E W := ⟨2,![4,33,27,23],![6,10,58,44]⟩
def cycle2_3 : CycleData E W := ⟨3,![5,29,20,10,11],![2,10,46,18,20]⟩
def cycle2_4 : CycleData E W := ⟨2,![12,21,30,17],![4,30,46,34]⟩
def cycle2_5 : CycleData E W := ⟨4,![24,25,14,13,22,28],![8,20,32,16,30,44]⟩
def cycle2_6 : CycleData E W := ⟨3,![31,16,15,26,32],![22,34,31,32,58]⟩
def data2 : PartitionData E W := ⟨7,![cycle2_0,cycle2_1,cycle2_2,cycle2_3,cycle2_4,cycle2_5,cycle2_6]⟩
lemma valid2 : data2.Valid src2 dst2 Finset.univ := by decide +kernel
lemma src_eq2 : src2 = src (unkey (representativeKey 2)) := by decide +kernel
lemma dst_eq2 : dst2 = dst (unkey (representativeKey 2)) := by decide +kernel
lemma certificate2 : Certificate 2 := by
  refine ⟨data2,?_,?_⟩
  · rw [← src_eq2,← dst_eq2]
    exact valid2
  · decide +kernel

def src3 : E → W := ![2,4,8,3,10,6,2,20,18,3,16,22,4,30,16,32,31,34,6,31,18,46,30,44,8,20,32,58,44,10,22,46,58,34]
def dst3 : E → W := ![4,8,3,10,6,2,20,18,3,16,22,2,30,16,32,31,34,4,31,18,46,30,44,6,20,32,58,44,8,22,46,58,34,10]
def cycle3_0 : CycleData E W := ⟨4,![0,1,2,9,10,11],![2,4,8,3,16,22]⟩
def cycle3_1 : CycleData E W := ⟨3,![3,29,30,20,8],![3,10,22,46,18]⟩
def cycle3_2 : CycleData E W := ⟨2,![4,33,16,18],![6,10,34,31]⟩
def cycle3_3 : CycleData E W := ⟨3,![5,23,28,24,6],![2,6,44,8,20]⟩
def cycle3_4 : CycleData E W := ⟨2,![7,25,15,19],![18,20,32,31]⟩
def cycle3_5 : CycleData E W := ⟨4,![12,13,14,26,32,17],![4,30,16,32,58,34]⟩
def cycle3_6 : CycleData E W := ⟨2,![21,31,27,22],![30,46,58,44]⟩
def data3 : PartitionData E W := ⟨7,![cycle3_0,cycle3_1,cycle3_2,cycle3_3,cycle3_4,cycle3_5,cycle3_6]⟩
lemma valid3 : data3.Valid src3 dst3 Finset.univ := by decide +kernel
lemma src_eq3 : src3 = src (unkey (representativeKey 3)) := by decide +kernel
lemma dst_eq3 : dst3 = dst (unkey (representativeKey 3)) := by decide +kernel
lemma certificate3 : Certificate 3 := by
  refine ⟨data3,?_,?_⟩
  · rw [← src_eq3,← dst_eq3]
    exact valid3
  · decide +kernel

def src4 : E → W := ![2,4,8,3,10,6,2,20,18,3,16,22,4,30,16,32,31,34,6,31,18,46,30,44,8,20,32,58,44,10,34,22,46,58]
def dst4 : E → W := ![4,8,3,10,6,2,20,18,3,16,22,2,30,16,32,31,34,4,31,18,46,30,44,6,20,32,58,44,8,34,22,46,58,10]
def cycle4_0 : CycleData E W := ⟨4,![0,1,2,9,10,11],![2,4,8,3,16,22]⟩
def cycle4_1 : CycleData E W := ⟨3,![3,33,32,20,8],![3,10,58,46,18]⟩
def cycle4_2 : CycleData E W := ⟨2,![4,29,16,18],![6,10,34,31]⟩
def cycle4_3 : CycleData E W := ⟨3,![5,23,28,24,6],![2,6,44,8,20]⟩
def cycle4_4 : CycleData E W := ⟨2,![7,25,15,19],![18,20,32,31]⟩
def cycle4_5 : CycleData E W := ⟨3,![12,21,31,30,17],![4,30,46,22,34]⟩
def cycle4_6 : CycleData E W := ⟨3,![13,22,27,26,14],![16,30,44,58,32]⟩
def data4 : PartitionData E W := ⟨7,![cycle4_0,cycle4_1,cycle4_2,cycle4_3,cycle4_4,cycle4_5,cycle4_6]⟩
lemma valid4 : data4.Valid src4 dst4 Finset.univ := by decide +kernel
lemma src_eq4 : src4 = src (unkey (representativeKey 4)) := by decide +kernel
lemma dst_eq4 : dst4 = dst (unkey (representativeKey 4)) := by decide +kernel
lemma certificate4 : Certificate 4 := by
  refine ⟨data4,?_,?_⟩
  · rw [← src_eq4,← dst_eq4]
    exact valid4
  · decide +kernel

def src5 : E → W := ![2,4,8,3,10,6,2,20,18,3,16,22,4,30,16,32,31,34,6,31,18,46,30,44,8,20,32,58,44,10,34,46,22,58]
def dst5 : E → W := ![4,8,3,10,6,2,20,18,3,16,22,2,30,16,32,31,34,4,31,18,46,30,44,6,20,32,58,44,8,34,46,22,58,10]
def cycle5_0 : CycleData E W := ⟨4,![0,1,2,9,10,11],![2,4,8,3,16,22]⟩
def cycle5_1 : CycleData E W := ⟨4,![3,33,32,31,20,8],![3,10,58,22,46,18]⟩
def cycle5_2 : CycleData E W := ⟨2,![4,29,16,18],![6,10,34,31]⟩
def cycle5_3 : CycleData E W := ⟨3,![5,23,28,24,6],![2,6,44,8,20]⟩
def cycle5_4 : CycleData E W := ⟨2,![7,25,15,19],![18,20,32,31]⟩
def cycle5_5 : CycleData E W := ⟨2,![12,21,30,17],![4,30,46,34]⟩
def cycle5_6 : CycleData E W := ⟨3,![13,22,27,26,14],![16,30,44,58,32]⟩
def data5 : PartitionData E W := ⟨7,![cycle5_0,cycle5_1,cycle5_2,cycle5_3,cycle5_4,cycle5_5,cycle5_6]⟩
lemma valid5 : data5.Valid src5 dst5 Finset.univ := by decide +kernel
lemma src_eq5 : src5 = src (unkey (representativeKey 5)) := by decide +kernel
lemma dst_eq5 : dst5 = dst (unkey (representativeKey 5)) := by decide +kernel
lemma certificate5 : Certificate 5 := by
  refine ⟨data5,?_,?_⟩
  · rw [← src_eq5,← dst_eq5]
    exact valid5
  · decide +kernel

def src6 : E → W := ![2,4,8,3,10,6,2,20,18,3,16,22,4,30,16,32,31,34,6,31,18,46,30,44,8,20,32,58,44,10,46,34,22,58]
def dst6 : E → W := ![4,8,3,10,6,2,20,18,3,16,22,2,30,16,32,31,34,4,31,18,46,30,44,6,20,32,58,44,8,46,34,22,58,10]
def cycle6_0 : CycleData E W := ⟨2,![0,1,24,6],![2,4,8,20]⟩
def cycle6_1 : CycleData E W := ⟨3,![2,28,22,13,9],![3,8,44,30,16]⟩
def cycle6_2 : CycleData E W := ⟨2,![3,29,20,8],![3,10,46,18]⟩
def cycle6_3 : CycleData E W := ⟨2,![4,33,27,23],![6,10,58,44]⟩
def cycle6_4 : CycleData E W := ⟨3,![5,18,16,31,11],![2,6,31,34,22]⟩
def cycle6_5 : CycleData E W := ⟨2,![7,25,15,19],![18,20,32,31]⟩
def cycle6_6 : CycleData E W := ⟨2,![10,32,26,14],![16,22,58,32]⟩
def cycle6_7 : CycleData E W := ⟨2,![12,21,30,17],![4,30,46,34]⟩
def data6 : PartitionData E W := ⟨8,![cycle6_0,cycle6_1,cycle6_2,cycle6_3,cycle6_4,cycle6_5,cycle6_6,cycle6_7]⟩
lemma valid6 : data6.Valid src6 dst6 Finset.univ := by decide +kernel
lemma src_eq6 : src6 = src (unkey (representativeKey 6)) := by decide +kernel
lemma dst_eq6 : dst6 = dst (unkey (representativeKey 6)) := by decide +kernel
lemma certificate6 : Certificate 6 := by
  refine ⟨data6,?_,?_⟩
  · rw [← src_eq6,← dst_eq6]
    exact valid6
  · decide +kernel

def src7 : E → W := ![2,4,8,3,10,6,2,20,18,3,16,22,4,30,16,32,31,34,6,31,18,46,30,44,8,20,44,58,32,10,34,46,22,58]
def dst7 : E → W := ![4,8,3,10,6,2,20,18,3,16,22,2,30,16,32,31,34,4,31,18,46,30,44,6,20,44,58,32,8,34,46,22,58,10]
def cycle7_0 : CycleData E W := ⟨4,![0,1,2,9,10,11],![2,4,8,3,16,22]⟩
def cycle7_1 : CycleData E W := ⟨4,![3,33,32,31,20,8],![3,10,58,22,46,18]⟩
def cycle7_2 : CycleData E W := ⟨2,![4,29,16,18],![6,10,34,31]⟩
def cycle7_3 : CycleData E W := ⟨2,![5,23,25,6],![2,6,44,20]⟩
def cycle7_4 : CycleData E W := ⟨3,![24,7,19,15,28],![8,20,18,31,32]⟩
def cycle7_5 : CycleData E W := ⟨2,![12,21,30,17],![4,30,46,34]⟩
def cycle7_6 : CycleData E W := ⟨3,![13,22,26,27,14],![16,30,44,58,32]⟩
def data7 : PartitionData E W := ⟨7,![cycle7_0,cycle7_1,cycle7_2,cycle7_3,cycle7_4,cycle7_5,cycle7_6]⟩
lemma valid7 : data7.Valid src7 dst7 Finset.univ := by decide +kernel
lemma src_eq7 : src7 = src (unkey (representativeKey 7)) := by decide +kernel
lemma dst_eq7 : dst7 = dst (unkey (representativeKey 7)) := by decide +kernel
lemma certificate7 : Certificate 7 := by
  refine ⟨data7,?_,?_⟩
  · rw [← src_eq7,← dst_eq7]
    exact valid7
  · decide +kernel

def src8 : E → W := ![2,4,8,3,10,6,2,20,18,3,16,22,4,30,16,32,31,34,6,31,18,46,30,44,8,32,20,44,58,10,34,58,22,46]
def dst8 : E → W := ![4,8,3,10,6,2,20,18,3,16,22,2,30,16,32,31,34,4,31,18,46,30,44,6,32,20,44,58,8,34,58,22,46,10]
def cycle8_0 : CycleData E W := ⟨3,![0,12,13,10,11],![2,4,30,16,22]⟩
def cycle8_1 : CycleData E W := ⟨2,![1,28,30,17],![4,8,58,34]⟩
def cycle8_2 : CycleData E W := ⟨2,![2,24,14,9],![3,8,32,16]⟩
def cycle8_3 : CycleData E W := ⟨2,![3,33,20,8],![3,10,46,18]⟩
def cycle8_4 : CycleData E W := ⟨2,![4,29,16,18],![6,10,34,31]⟩
def cycle8_5 : CycleData E W := ⟨2,![5,23,26,6],![2,6,44,20]⟩
def cycle8_6 : CycleData E W := ⟨2,![7,25,15,19],![18,20,32,31]⟩
def cycle8_7 : CycleData E W := ⟨3,![31,27,22,21,32],![22,58,44,30,46]⟩
def data8 : PartitionData E W := ⟨8,![cycle8_0,cycle8_1,cycle8_2,cycle8_3,cycle8_4,cycle8_5,cycle8_6,cycle8_7]⟩
lemma valid8 : data8.Valid src8 dst8 Finset.univ := by decide +kernel
lemma src_eq8 : src8 = src (unkey (representativeKey 8)) := by decide +kernel
lemma dst_eq8 : dst8 = dst (unkey (representativeKey 8)) := by decide +kernel
lemma certificate8 : Certificate 8 := by
  refine ⟨data8,?_,?_⟩
  · rw [← src_eq8,← dst_eq8]
    exact valid8
  · decide +kernel

def src9 : E → W := ![2,4,8,3,10,6,2,20,18,3,16,22,4,30,16,32,31,34,6,31,18,46,30,44,8,32,20,44,58,10,46,22,34,58]
def dst9 : E → W := ![4,8,3,10,6,2,20,18,3,16,22,2,30,16,32,31,34,4,31,18,46,30,44,6,32,20,44,58,8,46,22,34,58,10]
def cycle9_0 : CycleData E W := ⟨3,![0,12,22,26,6],![2,4,30,44,20]⟩
def cycle9_1 : CycleData E W := ⟨2,![1,28,32,17],![4,8,58,34]⟩
def cycle9_2 : CycleData E W := ⟨2,![2,24,14,9],![3,8,32,16]⟩
def cycle9_3 : CycleData E W := ⟨2,![3,29,20,8],![3,10,46,18]⟩
def cycle9_4 : CycleData E W := ⟨2,![4,33,27,23],![6,10,58,44]⟩
def cycle9_5 : CycleData E W := ⟨3,![5,18,16,31,11],![2,6,31,34,22]⟩
def cycle9_6 : CycleData E W := ⟨2,![7,25,15,19],![18,20,32,31]⟩
def cycle9_7 : CycleData E W := ⟨2,![10,30,21,13],![16,22,46,30]⟩
def data9 : PartitionData E W := ⟨8,![cycle9_0,cycle9_1,cycle9_2,cycle9_3,cycle9_4,cycle9_5,cycle9_6,cycle9_7]⟩
lemma valid9 : data9.Valid src9 dst9 Finset.univ := by decide +kernel
lemma src_eq9 : src9 = src (unkey (representativeKey 9)) := by decide +kernel
lemma dst_eq9 : dst9 = dst (unkey (representativeKey 9)) := by decide +kernel
lemma certificate9 : Certificate 9 := by
  refine ⟨data9,?_,?_⟩
  · rw [← src_eq9,← dst_eq9]
    exact valid9
  · decide +kernel
#print axioms certificate9
end Erdos184Work.SixRepresentativeCertificates2

import Submission.SixRepresentativeCertificates1Base
namespace Erdos184Work.SixRepresentativeCertificates1
open PureSixRowModel1 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src150 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,16,34,32,6,30,44,18,46,8,20,44,58,32,10,34,46,22,58]
def dst150 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,16,34,32,4,30,44,18,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle150_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle150_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle150_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle150_3 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle150_4 : CycleData E W := ⟨2,![7,23,18,13],![16,20,44,30]⟩
def cycle150_5 : CycleData E W := ⟨4,![12,17,21,28,15,16],![4,30,6,46,34,32]⟩
def cycle150_6 : CycleData E W := ⟨3,![19,24,30,29,20],![18,44,58,22,46]⟩
def data150 : PartitionData E W := ⟨7,![cycle150_0,cycle150_1,cycle150_2,cycle150_3,cycle150_4,cycle150_5,cycle150_6]⟩
lemma valid150 : data150.Valid src150 dst150 Finset.univ := by decide +kernel
lemma src_eq150 : src150 = src (unkey (representativeKey 150)) := by decide +kernel
lemma dst_eq150 : dst150 = dst (unkey (representativeKey 150)) := by decide +kernel
lemma certificate150 : Certificate 150 := by
  refine ⟨data150,?_,?_⟩
  · rw [← src_eq150,← dst_eq150]
    exact valid150
  · decide +kernel

def src151 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,16,34,32,6,30,44,18,46,8,20,44,58,32,10,46,34,22,58]
def dst151 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,16,34,32,4,30,44,18,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle151_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle151_1 : CycleData E W := ⟨4,![1,16,15,28,21,2],![3,4,32,34,46,6]⟩
def cycle151_2 : CycleData E W := ⟨3,![3,22,23,18,17],![6,8,20,44,30]⟩
def cycle151_3 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle151_4 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle151_5 : CycleData E W := ⟨2,![7,8,29,14],![16,20,22,34]⟩
def cycle151_6 : CycleData E W := ⟨3,![9,30,24,19,10],![3,22,58,44,18]⟩
def data151 : PartitionData E W := ⟨7,![cycle151_0,cycle151_1,cycle151_2,cycle151_3,cycle151_4,cycle151_5,cycle151_6]⟩
lemma valid151 : data151.Valid src151 dst151 Finset.univ := by decide +kernel
lemma src_eq151 : src151 = src (unkey (representativeKey 151)) := by decide +kernel
lemma dst_eq151 : dst151 = dst (unkey (representativeKey 151)) := by decide +kernel
lemma certificate151 : Certificate 151 := by
  refine ⟨data151,?_,?_⟩
  · rw [← src_eq151,← dst_eq151]
    exact valid151
  · decide +kernel

def src152 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,16,34,32,6,44,18,30,46,8,20,44,58,32,10,34,46,22,58]
def dst152 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,16,34,32,4,44,18,30,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle152_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle152_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle152_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle152_3 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle152_4 : CycleData E W := ⟨3,![7,23,18,19,13],![16,20,44,18,30]⟩
def cycle152_5 : CycleData E W := ⟨3,![12,20,28,15,16],![4,30,46,34,32]⟩
def cycle152_6 : CycleData E W := ⟨3,![17,24,30,29,21],![6,44,58,22,46]⟩
def data152 : PartitionData E W := ⟨7,![cycle152_0,cycle152_1,cycle152_2,cycle152_3,cycle152_4,cycle152_5,cycle152_6]⟩
lemma valid152 : data152.Valid src152 dst152 Finset.univ := by decide +kernel
lemma src_eq152 : src152 = src (unkey (representativeKey 152)) := by decide +kernel
lemma dst_eq152 : dst152 = dst (unkey (representativeKey 152)) := by decide +kernel
lemma certificate152 : Certificate 152 := by
  refine ⟨data152,?_,?_⟩
  · rw [← src_eq152,← dst_eq152]
    exact valid152
  · decide +kernel

def src153 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,16,34,32,6,44,30,18,46,8,20,44,58,32,10,34,46,22,58]
def dst153 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,16,34,32,4,44,30,18,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle153_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle153_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle153_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle153_3 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle153_4 : CycleData E W := ⟨2,![7,23,18,13],![16,20,44,30]⟩
def cycle153_5 : CycleData E W := ⟨4,![12,19,20,28,15,16],![4,30,18,46,34,32]⟩
def cycle153_6 : CycleData E W := ⟨3,![17,24,30,29,21],![6,44,58,22,46]⟩
def data153 : PartitionData E W := ⟨7,![cycle153_0,cycle153_1,cycle153_2,cycle153_3,cycle153_4,cycle153_5,cycle153_6]⟩
lemma valid153 : data153.Valid src153 dst153 Finset.univ := by decide +kernel
lemma src_eq153 : src153 = src (unkey (representativeKey 153)) := by decide +kernel
lemma dst_eq153 : dst153 = dst (unkey (representativeKey 153)) := by decide +kernel
lemma certificate153 : Certificate 153 := by
  refine ⟨data153,?_,?_⟩
  · rw [← src_eq153,← dst_eq153]
    exact valid153
  · decide +kernel

def src154 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,16,34,32,6,44,30,18,46,8,20,44,58,32,10,46,34,22,58]
def dst154 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,16,34,32,4,44,30,18,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle154_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle154_1 : CycleData E W := ⟨4,![1,16,15,28,21,2],![3,4,32,34,46,6]⟩
def cycle154_2 : CycleData E W := ⟨2,![3,22,23,17],![6,8,20,44]⟩
def cycle154_3 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle154_4 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle154_5 : CycleData E W := ⟨2,![7,8,29,14],![16,20,22,34]⟩
def cycle154_6 : CycleData E W := ⟨4,![9,30,24,18,19,10],![3,22,58,44,30,18]⟩
def data154 : PartitionData E W := ⟨7,![cycle154_0,cycle154_1,cycle154_2,cycle154_3,cycle154_4,cycle154_5,cycle154_6]⟩
lemma valid154 : data154.Valid src154 dst154 Finset.univ := by decide +kernel
lemma src_eq154 : src154 = src (unkey (representativeKey 154)) := by decide +kernel
lemma dst_eq154 : dst154 = dst (unkey (representativeKey 154)) := by decide +kernel
lemma certificate154 : Certificate 154 := by
  refine ⟨data154,?_,?_⟩
  · rw [← src_eq154,← dst_eq154]
    exact valid154
  · decide +kernel

def src155 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,32,16,34,6,30,46,18,44,8,20,44,58,32,10,46,22,34,58]
def dst155 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,32,16,34,4,30,46,18,44,6,20,44,58,32,8,46,22,34,58,10]
def cycle155_0 : CycleData E W := ⟨4,![0,1,9,8,7,6],![2,4,3,22,20,16]⟩
def cycle155_1 : CycleData E W := ⟨2,![2,21,20,10],![3,6,44,18]⟩
def cycle155_2 : CycleData E W := ⟨2,![3,26,13,17],![6,8,32,30]⟩
def cycle155_3 : CycleData E W := ⟨3,![4,31,24,23,22],![8,10,58,44,20]⟩
def cycle155_4 : CycleData E W := ⟨2,![5,27,19,11],![2,10,46,18]⟩
def cycle155_5 : CycleData E W := ⟨3,![12,18,28,29,16],![4,30,46,22,34]⟩
def cycle155_6 : CycleData E W := ⟨2,![14,25,30,15],![16,32,58,34]⟩
def data155 : PartitionData E W := ⟨7,![cycle155_0,cycle155_1,cycle155_2,cycle155_3,cycle155_4,cycle155_5,cycle155_6]⟩
lemma valid155 : data155.Valid src155 dst155 Finset.univ := by decide +kernel
lemma src_eq155 : src155 = src (unkey (representativeKey 155)) := by decide +kernel
lemma dst_eq155 : dst155 = dst (unkey (representativeKey 155)) := by decide +kernel
lemma certificate155 : Certificate 155 := by
  refine ⟨data155,?_,?_⟩
  · rw [← src_eq155,← dst_eq155]
    exact valid155
  · decide +kernel

def src156 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,32,16,34,6,30,46,18,44,8,20,44,58,32,10,46,34,22,58]
def dst156 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,32,16,34,4,30,46,18,44,6,20,44,58,32,8,46,34,22,58,10]
def cycle156_0 : CycleData E W := ⟨4,![0,1,9,8,7,6],![2,4,3,22,20,16]⟩
def cycle156_1 : CycleData E W := ⟨2,![2,21,20,10],![3,6,44,18]⟩
def cycle156_2 : CycleData E W := ⟨2,![3,26,13,17],![6,8,32,30]⟩
def cycle156_3 : CycleData E W := ⟨3,![4,31,24,23,22],![8,10,58,44,20]⟩
def cycle156_4 : CycleData E W := ⟨2,![5,27,19,11],![2,10,46,18]⟩
def cycle156_5 : CycleData E W := ⟨2,![12,18,28,16],![4,30,46,34]⟩
def cycle156_6 : CycleData E W := ⟨3,![14,25,30,29,15],![16,32,58,22,34]⟩
def data156 : PartitionData E W := ⟨7,![cycle156_0,cycle156_1,cycle156_2,cycle156_3,cycle156_4,cycle156_5,cycle156_6]⟩
lemma valid156 : data156.Valid src156 dst156 Finset.univ := by decide +kernel
lemma src_eq156 : src156 = src (unkey (representativeKey 156)) := by decide +kernel
lemma dst_eq156 : dst156 = dst (unkey (representativeKey 156)) := by decide +kernel
lemma certificate156 : Certificate 156 := by
  refine ⟨data156,?_,?_⟩
  · rw [← src_eq156,← dst_eq156]
    exact valid156
  · decide +kernel

def src157 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,32,16,34,6,44,18,30,46,8,20,44,58,32,10,34,46,22,58]
def dst157 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,32,16,34,4,44,18,30,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle157_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle157_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle157_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle157_3 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle157_4 : CycleData E W := ⟨4,![7,23,18,19,13,14],![16,20,44,18,30,32]⟩
def cycle157_5 : CycleData E W := ⟨2,![12,20,28,16],![4,30,46,34]⟩
def cycle157_6 : CycleData E W := ⟨3,![17,24,30,29,21],![6,44,58,22,46]⟩
def data157 : PartitionData E W := ⟨7,![cycle157_0,cycle157_1,cycle157_2,cycle157_3,cycle157_4,cycle157_5,cycle157_6]⟩
lemma valid157 : data157.Valid src157 dst157 Finset.univ := by decide +kernel
lemma src_eq157 : src157 = src (unkey (representativeKey 157)) := by decide +kernel
lemma dst_eq157 : dst157 = dst (unkey (representativeKey 157)) := by decide +kernel
lemma certificate157 : Certificate 157 := by
  refine ⟨data157,?_,?_⟩
  · rw [← src_eq157,← dst_eq157]
    exact valid157
  · decide +kernel

def src158 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,30,34,16,32,6,30,44,18,46,8,20,44,58,32,10,34,46,22,58]
def dst158 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,30,34,16,32,4,30,44,18,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle158_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle158_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle158_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle158_3 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle158_4 : CycleData E W := ⟨4,![12,18,23,7,15,16],![4,30,44,20,16,32]⟩
def cycle158_5 : CycleData E W := ⟨2,![17,13,28,21],![6,30,34,46]⟩
def cycle158_6 : CycleData E W := ⟨3,![19,24,30,29,20],![18,44,58,22,46]⟩
def data158 : PartitionData E W := ⟨7,![cycle158_0,cycle158_1,cycle158_2,cycle158_3,cycle158_4,cycle158_5,cycle158_6]⟩
lemma valid158 : data158.Valid src158 dst158 Finset.univ := by decide +kernel
lemma src_eq158 : src158 = src (unkey (representativeKey 158)) := by decide +kernel
lemma dst_eq158 : dst158 = dst (unkey (representativeKey 158)) := by decide +kernel
lemma certificate158 : Certificate 158 := by
  refine ⟨data158,?_,?_⟩
  · rw [← src_eq158,← dst_eq158]
    exact valid158
  · decide +kernel

def src159 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,16,30,34,6,30,44,18,46,8,20,44,58,32,10,22,34,58,46]
def dst159 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,16,30,34,4,30,44,18,46,6,20,44,58,32,8,22,34,58,46,10]
def cycle159_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle159_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle159_2 : CycleData E W := ⟨3,![5,4,26,13,6],![2,10,8,32,16]⟩
def cycle159_3 : CycleData E W := ⟨2,![7,23,18,14],![16,20,44,30]⟩
def cycle159_4 : CycleData E W := ⟨2,![12,25,29,16],![4,32,58,34]⟩
def cycle159_5 : CycleData E W := ⟨4,![17,15,28,27,31,21],![6,30,34,22,10,46]⟩
def cycle159_6 : CycleData E W := ⟨2,![19,24,30,20],![18,44,58,46]⟩
def data159 : PartitionData E W := ⟨7,![cycle159_0,cycle159_1,cycle159_2,cycle159_3,cycle159_4,cycle159_5,cycle159_6]⟩
lemma valid159 : data159.Valid src159 dst159 Finset.univ := by decide +kernel
lemma src_eq159 : src159 = src (unkey (representativeKey 159)) := by decide +kernel
lemma dst_eq159 : dst159 = dst (unkey (representativeKey 159)) := by decide +kernel
lemma certificate159 : Certificate 159 := by
  refine ⟨data159,?_,?_⟩
  · rw [← src_eq159,← dst_eq159]
    exact valid159
  · decide +kernel

def src160 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,16,30,34,6,30,44,18,46,8,20,44,58,32,10,34,22,58,46]
def dst160 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,16,30,34,4,30,44,18,46,6,20,44,58,32,8,34,22,58,46,10]
def cycle160_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle160_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle160_2 : CycleData E W := ⟨3,![5,4,26,13,6],![2,10,8,32,16]⟩
def cycle160_3 : CycleData E W := ⟨2,![7,23,18,14],![16,20,44,30]⟩
def cycle160_4 : CycleData E W := ⟨3,![12,25,29,28,16],![4,32,58,22,34]⟩
def cycle160_5 : CycleData E W := ⟨3,![17,15,27,31,21],![6,30,34,10,46]⟩
def cycle160_6 : CycleData E W := ⟨2,![19,24,30,20],![18,44,58,46]⟩
def data160 : PartitionData E W := ⟨7,![cycle160_0,cycle160_1,cycle160_2,cycle160_3,cycle160_4,cycle160_5,cycle160_6]⟩
lemma valid160 : data160.Valid src160 dst160 Finset.univ := by decide +kernel
lemma src_eq160 : src160 = src (unkey (representativeKey 160)) := by decide +kernel
lemma dst_eq160 : dst160 = dst (unkey (representativeKey 160)) := by decide +kernel
lemma certificate160 : Certificate 160 := by
  refine ⟨data160,?_,?_⟩
  · rw [← src_eq160,← dst_eq160]
    exact valid160
  · decide +kernel

def src161 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,16,30,34,6,30,44,18,46,8,20,44,58,32,10,46,22,34,58]
def dst161 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,16,30,34,4,30,44,18,46,6,20,44,58,32,8,46,22,34,58,10]
def cycle161_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle161_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle161_2 : CycleData E W := ⟨3,![5,4,26,13,6],![2,10,8,32,16]⟩
def cycle161_3 : CycleData E W := ⟨2,![7,23,18,14],![16,20,44,30]⟩
def cycle161_4 : CycleData E W := ⟨2,![12,25,30,16],![4,32,58,34]⟩
def cycle161_5 : CycleData E W := ⟨3,![17,15,29,28,21],![6,30,34,22,46]⟩
def cycle161_6 : CycleData E W := ⟨3,![27,20,19,24,31],![10,46,18,44,58]⟩
def data161 : PartitionData E W := ⟨7,![cycle161_0,cycle161_1,cycle161_2,cycle161_3,cycle161_4,cycle161_5,cycle161_6]⟩
lemma valid161 : data161.Valid src161 dst161 Finset.univ := by decide +kernel
lemma src_eq161 : src161 = src (unkey (representativeKey 161)) := by decide +kernel
lemma dst_eq161 : dst161 = dst (unkey (representativeKey 161)) := by decide +kernel
lemma certificate161 : Certificate 161 := by
  refine ⟨data161,?_,?_⟩
  · rw [← src_eq161,← dst_eq161]
    exact valid161
  · decide +kernel

def src162 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,16,30,34,6,30,44,18,46,8,20,44,58,32,10,46,34,22,58]
def dst162 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,16,30,34,4,30,44,18,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle162_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle162_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle162_2 : CycleData E W := ⟨3,![5,4,26,13,6],![2,10,8,32,16]⟩
def cycle162_3 : CycleData E W := ⟨2,![7,23,18,14],![16,20,44,30]⟩
def cycle162_4 : CycleData E W := ⟨3,![12,25,30,29,16],![4,32,58,22,34]⟩
def cycle162_5 : CycleData E W := ⟨2,![17,15,28,21],![6,30,34,46]⟩
def cycle162_6 : CycleData E W := ⟨3,![27,20,19,24,31],![10,46,18,44,58]⟩
def data162 : PartitionData E W := ⟨7,![cycle162_0,cycle162_1,cycle162_2,cycle162_3,cycle162_4,cycle162_5,cycle162_6]⟩
lemma valid162 : data162.Valid src162 dst162 Finset.univ := by decide +kernel
lemma src_eq162 : src162 = src (unkey (representativeKey 162)) := by decide +kernel
lemma dst_eq162 : dst162 = dst (unkey (representativeKey 162)) := by decide +kernel
lemma certificate162 : Certificate 162 := by
  refine ⟨data162,?_,?_⟩
  · rw [← src_eq162,← dst_eq162]
    exact valid162
  · decide +kernel

def src163 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,30,16,34,6,30,44,18,46,8,20,44,58,32,10,22,34,58,46]
def dst163 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,30,16,34,4,30,44,18,46,6,20,44,58,32,8,22,34,58,46,10]
def cycle163_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle163_1 : CycleData E W := ⟨4,![2,17,14,7,8,9],![3,6,30,16,20,22]⟩
def cycle163_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle163_3 : CycleData E W := ⟨3,![5,27,28,15,6],![2,10,22,34,16]⟩
def cycle163_4 : CycleData E W := ⟨2,![12,25,29,16],![4,32,58,34]⟩
def cycle163_5 : CycleData E W := ⟨3,![22,23,18,13,26],![8,20,44,30,32]⟩
def cycle163_6 : CycleData E W := ⟨2,![19,24,30,20],![18,44,58,46]⟩
def data163 : PartitionData E W := ⟨7,![cycle163_0,cycle163_1,cycle163_2,cycle163_3,cycle163_4,cycle163_5,cycle163_6]⟩
lemma valid163 : data163.Valid src163 dst163 Finset.univ := by decide +kernel
lemma src_eq163 : src163 = src (unkey (representativeKey 163)) := by decide +kernel
lemma dst_eq163 : dst163 = dst (unkey (representativeKey 163)) := by decide +kernel
lemma certificate163 : Certificate 163 := by
  refine ⟨data163,?_,?_⟩
  · rw [← src_eq163,← dst_eq163]
    exact valid163
  · decide +kernel

def src164 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,30,16,34,6,30,44,18,46,8,20,44,58,32,10,34,46,22,58]
def dst164 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,30,16,34,4,30,44,18,46,6,20,44,58,32,8,34,46,22,58,10]
def cycle164_0 : CycleData E W := ⟨2,![0,1,10,11],![2,4,3,18]⟩
def cycle164_1 : CycleData E W := ⟨3,![2,3,22,8,9],![3,6,8,20,22]⟩
def cycle164_2 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle164_3 : CycleData E W := ⟨2,![5,27,15,6],![2,10,34,16]⟩
def cycle164_4 : CycleData E W := ⟨2,![7,23,18,14],![16,20,44,30]⟩
def cycle164_5 : CycleData E W := ⟨4,![12,13,17,21,28,16],![4,32,30,6,46,34]⟩
def cycle164_6 : CycleData E W := ⟨3,![19,24,30,29,20],![18,44,58,22,46]⟩
def data164 : PartitionData E W := ⟨7,![cycle164_0,cycle164_1,cycle164_2,cycle164_3,cycle164_4,cycle164_5,cycle164_6]⟩
lemma valid164 : data164.Valid src164 dst164 Finset.univ := by decide +kernel
lemma src_eq164 : src164 = src (unkey (representativeKey 164)) := by decide +kernel
lemma dst_eq164 : dst164 = dst (unkey (representativeKey 164)) := by decide +kernel
lemma certificate164 : Certificate 164 := by
  refine ⟨data164,?_,?_⟩
  · rw [← src_eq164,← dst_eq164]
    exact valid164
  · decide +kernel

def src165 : E → W := ![2,4,3,6,8,10,2,16,20,22,3,18,4,32,30,16,34,6,30,44,18,46,8,20,44,58,32,10,46,34,22,58]
def dst165 : E → W := ![4,3,6,8,10,2,16,20,22,3,18,2,32,30,16,34,4,30,44,18,46,6,20,44,58,32,8,46,34,22,58,10]
def cycle165_0 : CycleData E W := ⟨3,![0,12,13,14,6],![2,4,32,30,16]⟩
def cycle165_1 : CycleData E W := ⟨3,![1,16,28,21,2],![3,4,34,46,6]⟩
def cycle165_2 : CycleData E W := ⟨3,![3,22,23,18,17],![6,8,20,44,30]⟩
def cycle165_3 : CycleData E W := ⟨2,![4,31,25,26],![8,10,58,32]⟩
def cycle165_4 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle165_5 : CycleData E W := ⟨2,![7,8,29,15],![16,20,22,34]⟩
def cycle165_6 : CycleData E W := ⟨3,![9,30,24,19,10],![3,22,58,44,18]⟩
def data165 : PartitionData E W := ⟨7,![cycle165_0,cycle165_1,cycle165_2,cycle165_3,cycle165_4,cycle165_5,cycle165_6]⟩
lemma valid165 : data165.Valid src165 dst165 Finset.univ := by decide +kernel
lemma src_eq165 : src165 = src (unkey (representativeKey 165)) := by decide +kernel
lemma dst_eq165 : dst165 = dst (unkey (representativeKey 165)) := by decide +kernel
lemma certificate165 : Certificate 165 := by
  refine ⟨data165,?_,?_⟩
  · rw [← src_eq165,← dst_eq165]
    exact valid165
  · decide +kernel

def src166 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,18,30,44,46,8,32,20,58,44,10,34,46,22,58]
def dst166 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,18,30,44,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle166_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle166_1 : CycleData E W := ⟨3,![1,16,28,21,2],![3,4,34,46,6]⟩
def cycle166_2 : CycleData E W := ⟨3,![3,26,19,18,17],![6,8,44,30,18]⟩
def cycle166_3 : CycleData E W := ⟨2,![4,27,15,22],![8,10,34,32]⟩
def cycle166_4 : CycleData E W := ⟨3,![5,31,24,10,11],![2,10,58,20,18]⟩
def cycle166_5 : CycleData E W := ⟨3,![8,7,14,23,9],![3,22,16,32,20]⟩
def cycle166_6 : CycleData E W := ⟨2,![29,20,25,30],![22,46,44,58]⟩
def data166 : PartitionData E W := ⟨7,![cycle166_0,cycle166_1,cycle166_2,cycle166_3,cycle166_4,cycle166_5,cycle166_6]⟩
lemma valid166 : data166.Valid src166 dst166 Finset.univ := by decide +kernel
lemma src_eq166 : src166 = src (unkey (representativeKey 166)) := by decide +kernel
lemma dst_eq166 : dst166 = dst (unkey (representativeKey 166)) := by decide +kernel
lemma certificate166 : Certificate 166 := by
  refine ⟨data166,?_,?_⟩
  · rw [← src_eq166,← dst_eq166]
    exact valid166
  · decide +kernel

def src167 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,18,44,30,46,8,32,20,58,44,10,34,46,22,58]
def dst167 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,18,44,30,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle167_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle167_1 : CycleData E W := ⟨2,![2,21,29,8],![3,6,46,22]⟩
def cycle167_2 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,18]⟩
def cycle167_3 : CycleData E W := ⟨3,![5,4,22,14,6],![2,10,8,32,16]⟩
def cycle167_4 : CycleData E W := ⟨3,![7,30,25,19,13],![16,22,58,44,30]⟩
def cycle167_5 : CycleData E W := ⟨2,![12,20,28,16],![4,30,46,34]⟩
def cycle167_6 : CycleData E W := ⟨3,![27,15,23,24,31],![10,34,32,20,58]⟩
def data167 : PartitionData E W := ⟨7,![cycle167_0,cycle167_1,cycle167_2,cycle167_3,cycle167_4,cycle167_5,cycle167_6]⟩
lemma valid167 : data167.Valid src167 dst167 Finset.univ := by decide +kernel
lemma src_eq167 : src167 = src (unkey (representativeKey 167)) := by decide +kernel
lemma dst_eq167 : dst167 = dst (unkey (representativeKey 167)) := by decide +kernel
lemma certificate167 : Certificate 167 := by
  refine ⟨data167,?_,?_⟩
  · rw [← src_eq167,← dst_eq167]
    exact valid167
  · decide +kernel

def src168 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,18,44,46,30,8,20,58,44,32,10,34,58,22,46]
def dst168 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,18,44,46,30,6,20,58,44,32,8,34,58,22,46,10]
def cycle168_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle168_1 : CycleData E W := ⟨3,![1,16,28,23,9],![3,4,34,58,20]⟩
def cycle168_2 : CycleData E W := ⟨3,![2,21,20,30,8],![3,6,30,46,22]⟩
def cycle168_3 : CycleData E W := ⟨2,![3,22,10,17],![6,8,20,18]⟩
def cycle168_4 : CycleData E W := ⟨2,![4,27,15,26],![8,10,34,32]⟩
def cycle168_5 : CycleData E W := ⟨3,![5,31,19,18,11],![2,10,46,44,18]⟩
def cycle168_6 : CycleData E W := ⟨3,![7,29,24,25,14],![16,22,58,44,32]⟩
def data168 : PartitionData E W := ⟨7,![cycle168_0,cycle168_1,cycle168_2,cycle168_3,cycle168_4,cycle168_5,cycle168_6]⟩
lemma valid168 : data168.Valid src168 dst168 Finset.univ := by decide +kernel
lemma src_eq168 : src168 = src (unkey (representativeKey 168)) := by decide +kernel
lemma dst_eq168 : dst168 = dst (unkey (representativeKey 168)) := by decide +kernel
lemma certificate168 : Certificate 168 := by
  refine ⟨data168,?_,?_⟩
  · rw [← src_eq168,← dst_eq168]
    exact valid168
  · decide +kernel

def src169 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,18,44,46,30,8,32,20,58,44,10,46,22,34,58]
def dst169 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,18,44,46,30,6,32,20,58,44,8,46,22,34,58,10]
def cycle169_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle169_1 : CycleData E W := ⟨2,![2,17,10,9],![3,6,18,20]⟩
def cycle169_2 : CycleData E W := ⟨3,![3,22,14,13,21],![6,8,32,16,30]⟩
def cycle169_3 : CycleData E W := ⟨3,![5,4,26,18,11],![2,10,8,44,18]⟩
def cycle169_4 : CycleData E W := ⟨3,![12,20,28,29,16],![4,30,46,22,34]⟩
def cycle169_5 : CycleData E W := ⟨2,![23,15,30,24],![20,32,34,58]⟩
def cycle169_6 : CycleData E W := ⟨2,![27,19,25,31],![10,46,44,58]⟩
def data169 : PartitionData E W := ⟨7,![cycle169_0,cycle169_1,cycle169_2,cycle169_3,cycle169_4,cycle169_5,cycle169_6]⟩
lemma valid169 : data169.Valid src169 dst169 Finset.univ := by decide +kernel
lemma src_eq169 : src169 = src (unkey (representativeKey 169)) := by decide +kernel
lemma dst_eq169 : dst169 = dst (unkey (representativeKey 169)) := by decide +kernel
lemma certificate169 : Certificate 169 := by
  refine ⟨data169,?_,?_⟩
  · rw [← src_eq169,← dst_eq169]
    exact valid169
  · decide +kernel

def src170 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,30,44,18,46,8,20,58,44,32,10,22,58,34,46]
def dst170 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,30,44,18,46,6,20,58,44,32,8,22,58,34,46,10]
def cycle170_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle170_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle170_2 : CycleData E W := ⟨4,![4,27,28,29,15,26],![8,10,22,58,34,32]⟩
def cycle170_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle170_4 : CycleData E W := ⟨2,![10,23,24,19],![18,20,58,44]⟩
def cycle170_5 : CycleData E W := ⟨3,![12,17,21,30,16],![4,30,6,46,34]⟩
def cycle170_6 : CycleData E W := ⟨2,![13,18,25,14],![16,30,44,32]⟩
def data170 : PartitionData E W := ⟨7,![cycle170_0,cycle170_1,cycle170_2,cycle170_3,cycle170_4,cycle170_5,cycle170_6]⟩
lemma valid170 : data170.Valid src170 dst170 Finset.univ := by decide +kernel
lemma src_eq170 : src170 = src (unkey (representativeKey 170)) := by decide +kernel
lemma dst_eq170 : dst170 = dst (unkey (representativeKey 170)) := by decide +kernel
lemma certificate170 : Certificate 170 := by
  refine ⟨data170,?_,?_⟩
  · rw [← src_eq170,← dst_eq170]
    exact valid170
  · decide +kernel

def src171 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,30,44,18,46,8,32,20,58,44,10,22,58,34,46]
def dst171 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,30,44,18,46,6,32,20,58,44,8,22,58,34,46,10]
def cycle171_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle171_1 : CycleData E W := ⟨3,![1,16,15,23,9],![3,4,34,32,20]⟩
def cycle171_2 : CycleData E W := ⟨4,![2,21,30,29,28,8],![3,6,46,34,58,22]⟩
def cycle171_3 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,30]⟩
def cycle171_4 : CycleData E W := ⟨3,![4,27,7,14,22],![8,10,22,16,32]⟩
def cycle171_5 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle171_6 : CycleData E W := ⟨2,![10,24,25,19],![18,20,58,44]⟩
def data171 : PartitionData E W := ⟨7,![cycle171_0,cycle171_1,cycle171_2,cycle171_3,cycle171_4,cycle171_5,cycle171_6]⟩
lemma valid171 : data171.Valid src171 dst171 Finset.univ := by decide +kernel
lemma src_eq171 : src171 = src (unkey (representativeKey 171)) := by decide +kernel
lemma dst_eq171 : dst171 = dst (unkey (representativeKey 171)) := by decide +kernel
lemma certificate171 : Certificate 171 := by
  refine ⟨data171,?_,?_⟩
  · rw [← src_eq171,← dst_eq171]
    exact valid171
  · decide +kernel

def src172 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,30,44,18,46,8,32,20,58,44,10,22,58,46,34]
def dst172 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,30,44,18,46,6,32,20,58,44,8,22,58,46,34,10]
def cycle172_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle172_1 : CycleData E W := ⟨3,![1,16,15,23,9],![3,4,34,32,20]⟩
def cycle172_2 : CycleData E W := ⟨3,![2,21,29,28,8],![3,6,46,58,22]⟩
def cycle172_3 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,30]⟩
def cycle172_4 : CycleData E W := ⟨3,![4,27,7,14,22],![8,10,22,16,32]⟩
def cycle172_5 : CycleData E W := ⟨3,![5,31,30,20,11],![2,10,34,46,18]⟩
def cycle172_6 : CycleData E W := ⟨2,![10,24,25,19],![18,20,58,44]⟩
def data172 : PartitionData E W := ⟨7,![cycle172_0,cycle172_1,cycle172_2,cycle172_3,cycle172_4,cycle172_5,cycle172_6]⟩
lemma valid172 : data172.Valid src172 dst172 Finset.univ := by decide +kernel
lemma src_eq172 : src172 = src (unkey (representativeKey 172)) := by decide +kernel
lemma dst_eq172 : dst172 = dst (unkey (representativeKey 172)) := by decide +kernel
lemma certificate172 : Certificate 172 := by
  refine ⟨data172,?_,?_⟩
  · rw [← src_eq172,← dst_eq172]
    exact valid172
  · decide +kernel

def src173 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,30,44,18,46,8,32,20,58,44,10,34,46,22,58]
def dst173 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,30,44,18,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle173_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle173_1 : CycleData E W := ⟨3,![1,16,15,23,9],![3,4,34,32,20]⟩
def cycle173_2 : CycleData E W := ⟨2,![2,21,29,8],![3,6,46,22]⟩
def cycle173_3 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,30]⟩
def cycle173_4 : CycleData E W := ⟨4,![4,31,30,7,14,22],![8,10,58,22,16,32]⟩
def cycle173_5 : CycleData E W := ⟨3,![5,27,28,20,11],![2,10,34,46,18]⟩
def cycle173_6 : CycleData E W := ⟨2,![10,24,25,19],![18,20,58,44]⟩
def data173 : PartitionData E W := ⟨7,![cycle173_0,cycle173_1,cycle173_2,cycle173_3,cycle173_4,cycle173_5,cycle173_6]⟩
lemma valid173 : data173.Valid src173 dst173 Finset.univ := by decide +kernel
lemma src_eq173 : src173 = src (unkey (representativeKey 173)) := by decide +kernel
lemma dst_eq173 : dst173 = dst (unkey (representativeKey 173)) := by decide +kernel
lemma certificate173 : Certificate 173 := by
  refine ⟨data173,?_,?_⟩
  · rw [← src_eq173,← dst_eq173]
    exact valid173
  · decide +kernel

def src174 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,30,44,18,46,8,32,20,58,44,10,46,34,22,58]
def dst174 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,30,44,18,46,6,32,20,58,44,8,46,34,22,58,10]
def cycle174_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle174_1 : CycleData E W := ⟨3,![1,16,15,23,9],![3,4,34,32,20]⟩
def cycle174_2 : CycleData E W := ⟨3,![2,21,28,29,8],![3,6,46,34,22]⟩
def cycle174_3 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,30]⟩
def cycle174_4 : CycleData E W := ⟨4,![4,31,30,7,14,22],![8,10,58,22,16,32]⟩
def cycle174_5 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle174_6 : CycleData E W := ⟨2,![10,24,25,19],![18,20,58,44]⟩
def data174 : PartitionData E W := ⟨7,![cycle174_0,cycle174_1,cycle174_2,cycle174_3,cycle174_4,cycle174_5,cycle174_6]⟩
lemma valid174 : data174.Valid src174 dst174 Finset.univ := by decide +kernel
lemma src_eq174 : src174 = src (unkey (representativeKey 174)) := by decide +kernel
lemma dst_eq174 : dst174 = dst (unkey (representativeKey 174)) := by decide +kernel
lemma certificate174 : Certificate 174 := by
  refine ⟨data174,?_,?_⟩
  · rw [← src_eq174,← dst_eq174]
    exact valid174
  · decide +kernel

def src175 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,30,46,18,44,8,20,58,44,32,10,22,58,34,46]
def dst175 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,30,46,18,44,6,20,58,44,32,8,22,58,34,46,10]
def cycle175_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle175_1 : CycleData E W := ⟨3,![2,21,20,10,9],![3,6,44,18,20]⟩
def cycle175_2 : CycleData E W := ⟨3,![3,26,14,13,17],![6,8,32,16,30]⟩
def cycle175_3 : CycleData E W := ⟨3,![4,27,28,23,22],![8,10,22,58,20]⟩
def cycle175_4 : CycleData E W := ⟨2,![5,31,19,11],![2,10,46,18]⟩
def cycle175_5 : CycleData E W := ⟨2,![12,18,30,16],![4,30,46,34]⟩
def cycle175_6 : CycleData E W := ⟨2,![15,29,24,25],![32,34,58,44]⟩
def data175 : PartitionData E W := ⟨7,![cycle175_0,cycle175_1,cycle175_2,cycle175_3,cycle175_4,cycle175_5,cycle175_6]⟩
lemma valid175 : data175.Valid src175 dst175 Finset.univ := by decide +kernel
lemma src_eq175 : src175 = src (unkey (representativeKey 175)) := by decide +kernel
lemma dst_eq175 : dst175 = dst (unkey (representativeKey 175)) := by decide +kernel
lemma certificate175 : Certificate 175 := by
  refine ⟨data175,?_,?_⟩
  · rw [← src_eq175,← dst_eq175]
    exact valid175
  · decide +kernel

def src176 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,30,46,18,44,8,20,58,44,32,10,34,58,22,46]
def dst176 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,30,46,18,44,6,20,58,44,32,8,34,58,22,46,10]
def cycle176_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle176_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle176_2 : CycleData E W := ⟨2,![4,27,15,26],![8,10,34,32]⟩
def cycle176_3 : CycleData E W := ⟨2,![5,31,19,11],![2,10,46,18]⟩
def cycle176_4 : CycleData E W := ⟨2,![10,23,24,20],![18,20,58,44]⟩
def cycle176_5 : CycleData E W := ⟨4,![12,18,30,29,28,16],![4,30,46,22,58,34]⟩
def cycle176_6 : CycleData E W := ⟨3,![17,13,14,25,21],![6,30,16,32,44]⟩
def data176 : PartitionData E W := ⟨7,![cycle176_0,cycle176_1,cycle176_2,cycle176_3,cycle176_4,cycle176_5,cycle176_6]⟩
lemma valid176 : data176.Valid src176 dst176 Finset.univ := by decide +kernel
lemma src_eq176 : src176 = src (unkey (representativeKey 176)) := by decide +kernel
lemma dst_eq176 : dst176 = dst (unkey (representativeKey 176)) := by decide +kernel
lemma certificate176 : Certificate 176 := by
  refine ⟨data176,?_,?_⟩
  · rw [← src_eq176,← dst_eq176]
    exact valid176
  · decide +kernel

def src177 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,20,58,44,32,10,22,58,34,46]
def dst177 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,20,58,44,32,8,22,58,34,46,10]
def cycle177_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle177_1 : CycleData E W := ⟨3,![2,17,24,28,8],![3,6,44,58,22]⟩
def cycle177_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle177_3 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle177_4 : CycleData E W := ⟨3,![12,19,20,30,16],![4,30,18,46,34]⟩
def cycle177_5 : CycleData E W := ⟨2,![13,18,25,14],![16,30,44,32]⟩
def cycle177_6 : CycleData E W := ⟨3,![22,23,29,15,26],![8,20,58,34,32]⟩
def data177 : PartitionData E W := ⟨7,![cycle177_0,cycle177_1,cycle177_2,cycle177_3,cycle177_4,cycle177_5,cycle177_6]⟩
lemma valid177 : data177.Valid src177 dst177 Finset.univ := by decide +kernel
lemma src_eq177 : src177 = src (unkey (representativeKey 177)) := by decide +kernel
lemma dst_eq177 : dst177 = dst (unkey (representativeKey 177)) := by decide +kernel
lemma certificate177 : Certificate 177 := by
  refine ⟨data177,?_,?_⟩
  · rw [← src_eq177,← dst_eq177]
    exact valid177
  · decide +kernel

def src178 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,20,58,44,32,10,22,58,46,34]
def dst178 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,20,58,44,32,8,22,58,46,34,10]
def cycle178_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle178_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle178_2 : CycleData E W := ⟨2,![4,31,15,26],![8,10,34,32]⟩
def cycle178_3 : CycleData E W := ⟨4,![5,27,28,23,10,11],![2,10,22,58,20,18]⟩
def cycle178_4 : CycleData E W := ⟨3,![12,19,20,30,16],![4,30,18,46,34]⟩
def cycle178_5 : CycleData E W := ⟨2,![13,18,25,14],![16,30,44,32]⟩
def cycle178_6 : CycleData E W := ⟨2,![17,24,29,21],![6,44,58,46]⟩
def data178 : PartitionData E W := ⟨7,![cycle178_0,cycle178_1,cycle178_2,cycle178_3,cycle178_4,cycle178_5,cycle178_6]⟩
lemma valid178 : data178.Valid src178 dst178 Finset.univ := by decide +kernel
lemma src_eq178 : src178 = src (unkey (representativeKey 178)) := by decide +kernel
lemma dst_eq178 : dst178 = dst (unkey (representativeKey 178)) := by decide +kernel
lemma certificate178 : Certificate 178 := by
  refine ⟨data178,?_,?_⟩
  · rw [← src_eq178,← dst_eq178]
    exact valid178
  · decide +kernel

def src179 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,32,20,58,44,10,22,34,58,46]
def dst179 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,32,20,58,44,8,22,34,58,46,10]
def cycle179_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle179_1 : CycleData E W := ⟨3,![2,21,30,24,9],![3,6,46,58,20]⟩
def cycle179_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle179_3 : CycleData E W := ⟨3,![4,27,28,15,22],![8,10,22,34,32]⟩
def cycle179_4 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle179_5 : CycleData E W := ⟨3,![13,19,10,23,14],![16,30,18,20,32]⟩
def cycle179_6 : CycleData E W := ⟨3,![12,18,25,29,16],![4,30,44,58,34]⟩
def data179 : PartitionData E W := ⟨7,![cycle179_0,cycle179_1,cycle179_2,cycle179_3,cycle179_4,cycle179_5,cycle179_6]⟩
lemma valid179 : data179.Valid src179 dst179 Finset.univ := by decide +kernel
lemma src_eq179 : src179 = src (unkey (representativeKey 179)) := by decide +kernel
lemma dst_eq179 : dst179 = dst (unkey (representativeKey 179)) := by decide +kernel
lemma certificate179 : Certificate 179 := by
  refine ⟨data179,?_,?_⟩
  · rw [← src_eq179,← dst_eq179]
    exact valid179
  · decide +kernel

def src180 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,32,20,58,44,10,22,58,34,46]
def dst180 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,32,20,58,44,8,22,58,34,46,10]
def cycle180_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle180_1 : CycleData E W := ⟨3,![2,17,25,28,8],![3,6,44,58,22]⟩
def cycle180_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle180_3 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle180_4 : CycleData E W := ⟨3,![12,19,20,30,16],![4,30,18,46,34]⟩
def cycle180_5 : CycleData E W := ⟨3,![22,14,13,18,26],![8,32,16,30,44]⟩
def cycle180_6 : CycleData E W := ⟨2,![23,15,29,24],![20,32,34,58]⟩
def data180 : PartitionData E W := ⟨7,![cycle180_0,cycle180_1,cycle180_2,cycle180_3,cycle180_4,cycle180_5,cycle180_6]⟩
lemma valid180 : data180.Valid src180 dst180 Finset.univ := by decide +kernel
lemma src_eq180 : src180 = src (unkey (representativeKey 180)) := by decide +kernel
lemma dst_eq180 : dst180 = dst (unkey (representativeKey 180)) := by decide +kernel
lemma certificate180 : Certificate 180 := by
  refine ⟨data180,?_,?_⟩
  · rw [← src_eq180,← dst_eq180]
    exact valid180
  · decide +kernel

def src181 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,32,20,58,44,10,22,58,46,34]
def dst181 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,32,20,58,44,8,22,58,46,34,10]
def cycle181_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle181_1 : CycleData E W := ⟨3,![2,21,29,28,8],![3,6,46,58,22]⟩
def cycle181_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle181_3 : CycleData E W := ⟨2,![4,31,15,22],![8,10,34,32]⟩
def cycle181_4 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle181_5 : CycleData E W := ⟨3,![12,19,20,30,16],![4,30,18,46,34]⟩
def cycle181_6 : CycleData E W := ⟨4,![13,18,25,24,23,14],![16,30,44,58,20,32]⟩
def data181 : PartitionData E W := ⟨7,![cycle181_0,cycle181_1,cycle181_2,cycle181_3,cycle181_4,cycle181_5,cycle181_6]⟩
lemma valid181 : data181.Valid src181 dst181 Finset.univ := by decide +kernel
lemma src_eq181 : src181 = src (unkey (representativeKey 181)) := by decide +kernel
lemma dst_eq181 : dst181 = dst (unkey (representativeKey 181)) := by decide +kernel
lemma certificate181 : Certificate 181 := by
  refine ⟨data181,?_,?_⟩
  · rw [← src_eq181,← dst_eq181]
    exact valid181
  · decide +kernel

def src182 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,32,20,58,44,10,34,46,22,58]
def dst182 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,32,20,58,44,8,34,46,22,58,10]
def cycle182_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle182_1 : CycleData E W := ⟨2,![2,21,29,8],![3,6,46,22]⟩
def cycle182_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle182_3 : CycleData E W := ⟨3,![5,4,22,14,6],![2,10,8,32,16]⟩
def cycle182_4 : CycleData E W := ⟨3,![7,30,25,18,13],![16,22,58,44,30]⟩
def cycle182_5 : CycleData E W := ⟨3,![12,19,20,28,16],![4,30,18,46,34]⟩
def cycle182_6 : CycleData E W := ⟨3,![27,15,23,24,31],![10,34,32,20,58]⟩
def data182 : PartitionData E W := ⟨7,![cycle182_0,cycle182_1,cycle182_2,cycle182_3,cycle182_4,cycle182_5,cycle182_6]⟩
lemma valid182 : data182.Valid src182 dst182 Finset.univ := by decide +kernel
lemma src_eq182 : src182 = src (unkey (representativeKey 182)) := by decide +kernel
lemma dst_eq182 : dst182 = dst (unkey (representativeKey 182)) := by decide +kernel
lemma certificate182 : Certificate 182 := by
  refine ⟨data182,?_,?_⟩
  · rw [← src_eq182,← dst_eq182]
    exact valid182
  · decide +kernel

def src183 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,32,34,6,44,30,18,46,8,32,20,58,44,10,46,34,22,58]
def dst183 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,32,34,4,44,30,18,46,6,32,20,58,44,8,46,34,22,58,10]
def cycle183_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle183_1 : CycleData E W := ⟨3,![1,16,15,23,9],![3,4,34,32,20]⟩
def cycle183_2 : CycleData E W := ⟨3,![2,21,28,29,8],![3,6,46,34,22]⟩
def cycle183_3 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle183_4 : CycleData E W := ⟨4,![4,31,30,7,14,22],![8,10,58,22,16,32]⟩
def cycle183_5 : CycleData E W := ⟨2,![5,27,20,11],![2,10,46,18]⟩
def cycle183_6 : CycleData E W := ⟨3,![10,24,25,18,19],![18,20,58,44,30]⟩
def data183 : PartitionData E W := ⟨7,![cycle183_0,cycle183_1,cycle183_2,cycle183_3,cycle183_4,cycle183_5,cycle183_6]⟩
lemma valid183 : data183.Valid src183 dst183 Finset.univ := by decide +kernel
lemma src_eq183 : src183 = src (unkey (representativeKey 183)) := by decide +kernel
lemma dst_eq183 : dst183 = dst (unkey (representativeKey 183)) := by decide +kernel
lemma certificate183 : Certificate 183 := by
  refine ⟨data183,?_,?_⟩
  · rw [← src_eq183,← dst_eq183]
    exact valid183
  · decide +kernel

def src184 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,34,32,6,30,44,18,46,8,32,20,58,44,10,22,58,34,46]
def dst184 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,34,32,4,30,44,18,46,6,32,20,58,44,8,22,58,34,46,10]
def cycle184_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle184_1 : CycleData E W := ⟨2,![1,16,23,9],![3,4,32,20]⟩
def cycle184_2 : CycleData E W := ⟨3,![2,3,4,27,8],![3,6,8,10,22]⟩
def cycle184_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle184_4 : CycleData E W := ⟨2,![7,28,29,14],![16,22,58,34]⟩
def cycle184_5 : CycleData E W := ⟨2,![10,24,25,19],![18,20,58,44]⟩
def cycle184_6 : CycleData E W := ⟨5,![17,18,26,22,15,30,21],![6,30,44,8,32,34,46]⟩
def data184 : PartitionData E W := ⟨7,![cycle184_0,cycle184_1,cycle184_2,cycle184_3,cycle184_4,cycle184_5,cycle184_6]⟩
lemma valid184 : data184.Valid src184 dst184 Finset.univ := by decide +kernel
lemma src_eq184 : src184 = src (unkey (representativeKey 184)) := by decide +kernel
lemma dst_eq184 : dst184 = dst (unkey (representativeKey 184)) := by decide +kernel
lemma certificate184 : Certificate 184 := by
  refine ⟨data184,?_,?_⟩
  · rw [← src_eq184,← dst_eq184]
    exact valid184
  · decide +kernel

def src185 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,34,32,6,30,44,18,46,8,32,20,58,44,10,22,58,46,34]
def dst185 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,34,32,4,30,44,18,46,6,32,20,58,44,8,22,58,46,34,10]
def cycle185_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,30,16]⟩
def cycle185_1 : CycleData E W := ⟨3,![1,16,22,3,2],![3,4,32,8,6]⟩
def cycle185_2 : CycleData E W := ⟨3,![5,4,26,19,11],![2,10,8,44,18]⟩
def cycle185_3 : CycleData E W := ⟨2,![27,7,14,31],![10,22,16,34]⟩
def cycle185_4 : CycleData E W := ⟨2,![8,28,24,9],![3,22,58,20]⟩
def cycle185_5 : CycleData E W := ⟨3,![10,23,15,30,20],![18,20,32,34,46]⟩
def cycle185_6 : CycleData E W := ⟨3,![17,18,25,29,21],![6,30,44,58,46]⟩
def data185 : PartitionData E W := ⟨7,![cycle185_0,cycle185_1,cycle185_2,cycle185_3,cycle185_4,cycle185_5,cycle185_6]⟩
lemma valid185 : data185.Valid src185 dst185 Finset.univ := by decide +kernel
lemma src_eq185 : src185 = src (unkey (representativeKey 185)) := by decide +kernel
lemma dst_eq185 : dst185 = dst (unkey (representativeKey 185)) := by decide +kernel
lemma certificate185 : Certificate 185 := by
  refine ⟨data185,?_,?_⟩
  · rw [← src_eq185,← dst_eq185]
    exact valid185
  · decide +kernel

def src186 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,16,34,32,6,44,30,18,46,8,32,20,58,44,10,22,58,34,46]
def dst186 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,16,34,32,4,44,30,18,46,6,32,20,58,44,8,22,58,34,46,10]
def cycle186_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle186_1 : CycleData E W := ⟨3,![2,17,25,28,8],![3,6,44,58,22]⟩
def cycle186_2 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle186_3 : CycleData E W := ⟨2,![5,27,7,6],![2,10,22,16]⟩
def cycle186_4 : CycleData E W := ⟨3,![12,18,26,22,16],![4,30,44,8,32]⟩
def cycle186_5 : CycleData E W := ⟨3,![13,19,20,30,14],![16,30,18,46,34]⟩
def cycle186_6 : CycleData E W := ⟨2,![23,15,29,24],![20,32,34,58]⟩
def data186 : PartitionData E W := ⟨7,![cycle186_0,cycle186_1,cycle186_2,cycle186_3,cycle186_4,cycle186_5,cycle186_6]⟩
lemma valid186 : data186.Valid src186 dst186 Finset.univ := by decide +kernel
lemma src_eq186 : src186 = src (unkey (representativeKey 186)) := by decide +kernel
lemma dst_eq186 : dst186 = dst (unkey (representativeKey 186)) := by decide +kernel
lemma certificate186 : Certificate 186 := by
  refine ⟨data186,?_,?_⟩
  · rw [← src_eq186,← dst_eq186]
    exact valid186
  · decide +kernel

def src187 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,30,18,44,46,8,20,58,32,44,10,34,46,22,58]
def dst187 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,30,18,44,46,6,20,58,32,44,8,34,46,22,58,10]
def cycle187_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle187_1 : CycleData E W := ⟨2,![2,21,29,8],![3,6,46,22]⟩
def cycle187_2 : CycleData E W := ⟨3,![3,26,19,18,17],![6,8,44,18,30]⟩
def cycle187_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle187_4 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle187_5 : CycleData E W := ⟨2,![7,30,24,15],![16,22,58,32]⟩
def cycle187_6 : CycleData E W := ⟨4,![12,13,28,20,25,16],![4,30,34,46,44,32]⟩
def data187 : PartitionData E W := ⟨7,![cycle187_0,cycle187_1,cycle187_2,cycle187_3,cycle187_4,cycle187_5,cycle187_6]⟩
lemma valid187 : data187.Valid src187 dst187 Finset.univ := by decide +kernel
lemma src_eq187 : src187 = src (unkey (representativeKey 187)) := by decide +kernel
lemma dst_eq187 : dst187 = dst (unkey (representativeKey 187)) := by decide +kernel
lemma certificate187 : Certificate 187 := by
  refine ⟨data187,?_,?_⟩
  · rw [← src_eq187,← dst_eq187]
    exact valid187
  · decide +kernel

def src188 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,30,18,44,46,8,20,58,44,32,10,34,46,22,58]
def dst188 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,30,18,44,46,6,20,58,44,32,8,34,46,22,58,10]
def cycle188_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle188_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle188_2 : CycleData E W := ⟨3,![4,27,14,15,26],![8,10,34,16,32]⟩
def cycle188_3 : CycleData E W := ⟨3,![5,31,23,10,11],![2,10,58,20,18]⟩
def cycle188_4 : CycleData E W := ⟨3,![12,18,19,25,16],![4,30,18,44,32]⟩
def cycle188_5 : CycleData E W := ⟨2,![17,13,28,21],![6,30,34,46]⟩
def cycle188_6 : CycleData E W := ⟨2,![29,20,24,30],![22,46,44,58]⟩
def data188 : PartitionData E W := ⟨7,![cycle188_0,cycle188_1,cycle188_2,cycle188_3,cycle188_4,cycle188_5,cycle188_6]⟩
lemma valid188 : data188.Valid src188 dst188 Finset.univ := by decide +kernel
lemma src_eq188 : src188 = src (unkey (representativeKey 188)) := by decide +kernel
lemma dst_eq188 : dst188 = dst (unkey (representativeKey 188)) := by decide +kernel
lemma certificate188 : Certificate 188 := by
  refine ⟨data188,?_,?_⟩
  · rw [← src_eq188,← dst_eq188]
    exact valid188
  · decide +kernel

def src189 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,30,44,18,46,8,20,32,58,44,10,22,58,46,34]
def dst189 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,30,44,18,46,6,20,32,58,44,8,22,58,46,34,10]
def cycle189_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle189_1 : CycleData E W := ⟨3,![2,3,4,27,8],![3,6,8,10,22]⟩
def cycle189_2 : CycleData E W := ⟨2,![5,31,14,6],![2,10,34,16]⟩
def cycle189_3 : CycleData E W := ⟨2,![7,28,24,15],![16,22,58,32]⟩
def cycle189_4 : CycleData E W := ⟨4,![12,18,26,22,23,16],![4,30,44,8,20,32]⟩
def cycle189_5 : CycleData E W := ⟨2,![17,13,30,21],![6,30,34,46]⟩
def cycle189_6 : CycleData E W := ⟨2,![19,25,29,20],![18,44,58,46]⟩
def data189 : PartitionData E W := ⟨7,![cycle189_0,cycle189_1,cycle189_2,cycle189_3,cycle189_4,cycle189_5,cycle189_6]⟩
lemma valid189 : data189.Valid src189 dst189 Finset.univ := by decide +kernel
lemma src_eq189 : src189 = src (unkey (representativeKey 189)) := by decide +kernel
lemma dst_eq189 : dst189 = dst (unkey (representativeKey 189)) := by decide +kernel
lemma certificate189 : Certificate 189 := by
  refine ⟨data189,?_,?_⟩
  · rw [← src_eq189,← dst_eq189]
    exact valid189
  · decide +kernel

def src190 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,30,44,18,46,8,20,58,44,32,10,34,46,22,58]
def dst190 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,30,44,18,46,6,20,58,44,32,8,34,46,22,58,10]
def cycle190_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle190_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle190_2 : CycleData E W := ⟨3,![4,27,14,15,26],![8,10,34,16,32]⟩
def cycle190_3 : CycleData E W := ⟨3,![5,31,23,10,11],![2,10,58,20,18]⟩
def cycle190_4 : CycleData E W := ⟨2,![12,18,25,16],![4,30,44,32]⟩
def cycle190_5 : CycleData E W := ⟨2,![17,13,28,21],![6,30,34,46]⟩
def cycle190_6 : CycleData E W := ⟨3,![19,24,30,29,20],![18,44,58,22,46]⟩
def data190 : PartitionData E W := ⟨7,![cycle190_0,cycle190_1,cycle190_2,cycle190_3,cycle190_4,cycle190_5,cycle190_6]⟩
lemma valid190 : data190.Valid src190 dst190 Finset.univ := by decide +kernel
lemma src_eq190 : src190 = src (unkey (representativeKey 190)) := by decide +kernel
lemma dst_eq190 : dst190 = dst (unkey (representativeKey 190)) := by decide +kernel
lemma certificate190 : Certificate 190 := by
  refine ⟨data190,?_,?_⟩
  · rw [← src_eq190,← dst_eq190]
    exact valid190
  · decide +kernel

def src191 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,44,30,18,46,8,20,32,58,44,10,22,58,46,34]
def dst191 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,44,30,18,46,6,20,32,58,44,8,22,58,46,34,10]
def cycle191_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle191_1 : CycleData E W := ⟨3,![2,3,4,27,8],![3,6,8,10,22]⟩
def cycle191_2 : CycleData E W := ⟨2,![5,31,14,6],![2,10,34,16]⟩
def cycle191_3 : CycleData E W := ⟨2,![7,28,24,15],![16,22,58,32]⟩
def cycle191_4 : CycleData E W := ⟨4,![12,18,26,22,23,16],![4,30,44,8,20,32]⟩
def cycle191_5 : CycleData E W := ⟨2,![19,13,30,20],![18,30,34,46]⟩
def cycle191_6 : CycleData E W := ⟨2,![17,25,29,21],![6,44,58,46]⟩
def data191 : PartitionData E W := ⟨7,![cycle191_0,cycle191_1,cycle191_2,cycle191_3,cycle191_4,cycle191_5,cycle191_6]⟩
lemma valid191 : data191.Valid src191 dst191 Finset.univ := by decide +kernel
lemma src_eq191 : src191 = src (unkey (representativeKey 191)) := by decide +kernel
lemma dst_eq191 : dst191 = dst (unkey (representativeKey 191)) := by decide +kernel
lemma certificate191 : Certificate 191 := by
  refine ⟨data191,?_,?_⟩
  · rw [← src_eq191,← dst_eq191]
    exact valid191
  · decide +kernel

def src192 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,44,30,18,46,8,20,58,32,44,10,22,58,46,34]
def dst192 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,44,30,18,46,6,20,58,32,44,8,22,58,46,34,10]
def cycle192_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle192_1 : CycleData E W := ⟨3,![2,21,20,10,9],![3,6,46,18,20]⟩
def cycle192_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle192_3 : CycleData E W := ⟨3,![4,27,28,23,22],![8,10,22,58,20]⟩
def cycle192_4 : CycleData E W := ⟨3,![5,31,13,19,11],![2,10,34,30,18]⟩
def cycle192_5 : CycleData E W := ⟨2,![12,18,25,16],![4,30,44,32]⟩
def cycle192_6 : CycleData E W := ⟨3,![14,30,29,24,15],![16,34,46,58,32]⟩
def data192 : PartitionData E W := ⟨7,![cycle192_0,cycle192_1,cycle192_2,cycle192_3,cycle192_4,cycle192_5,cycle192_6]⟩
lemma valid192 : data192.Valid src192 dst192 Finset.univ := by decide +kernel
lemma src_eq192 : src192 = src (unkey (representativeKey 192)) := by decide +kernel
lemma dst_eq192 : dst192 = dst (unkey (representativeKey 192)) := by decide +kernel
lemma certificate192 : Certificate 192 := by
  refine ⟨data192,?_,?_⟩
  · rw [← src_eq192,← dst_eq192]
    exact valid192
  · decide +kernel

def src193 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,44,30,18,46,8,20,58,32,44,10,34,46,22,58]
def dst193 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,44,30,18,46,6,20,58,32,44,8,34,46,22,58,10]
def cycle193_0 : CycleData E W := ⟨3,![0,1,9,10,11],![2,4,3,20,18]⟩
def cycle193_1 : CycleData E W := ⟨2,![2,21,29,8],![3,6,46,22]⟩
def cycle193_2 : CycleData E W := ⟨1,![3,26,17],![6,8,44]⟩
def cycle193_3 : CycleData E W := ⟨2,![4,31,23,22],![8,10,58,20]⟩
def cycle193_4 : CycleData E W := ⟨2,![5,27,14,6],![2,10,34,16]⟩
def cycle193_5 : CycleData E W := ⟨2,![7,30,24,15],![16,22,58,32]⟩
def cycle193_6 : CycleData E W := ⟨2,![12,18,25,16],![4,30,44,32]⟩
def cycle193_7 : CycleData E W := ⟨2,![19,13,28,20],![18,30,34,46]⟩
def data193 : PartitionData E W := ⟨8,![cycle193_0,cycle193_1,cycle193_2,cycle193_3,cycle193_4,cycle193_5,cycle193_6,cycle193_7]⟩
lemma valid193 : data193.Valid src193 dst193 Finset.univ := by decide +kernel
lemma src_eq193 : src193 = src (unkey (representativeKey 193)) := by decide +kernel
lemma dst_eq193 : dst193 = dst (unkey (representativeKey 193)) := by decide +kernel
lemma certificate193 : Certificate 193 := by
  refine ⟨data193,?_,?_⟩
  · rw [← src_eq193,← dst_eq193]
    exact valid193
  · decide +kernel

def src194 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,30,34,16,32,6,44,30,18,46,8,20,58,44,32,10,34,46,22,58]
def dst194 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,30,34,16,32,4,44,30,18,46,6,20,58,44,32,8,34,46,22,58,10]
def cycle194_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle194_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle194_2 : CycleData E W := ⟨3,![4,27,14,15,26],![8,10,34,16,32]⟩
def cycle194_3 : CycleData E W := ⟨3,![5,31,23,10,11],![2,10,58,20,18]⟩
def cycle194_4 : CycleData E W := ⟨2,![12,18,25,16],![4,30,44,32]⟩
def cycle194_5 : CycleData E W := ⟨2,![19,13,28,20],![18,30,34,46]⟩
def cycle194_6 : CycleData E W := ⟨3,![17,24,30,29,21],![6,44,58,22,46]⟩
def data194 : PartitionData E W := ⟨7,![cycle194_0,cycle194_1,cycle194_2,cycle194_3,cycle194_4,cycle194_5,cycle194_6]⟩
lemma valid194 : data194.Valid src194 dst194 Finset.univ := by decide +kernel
lemma src_eq194 : src194 = src (unkey (representativeKey 194)) := by decide +kernel
lemma dst_eq194 : dst194 = dst (unkey (representativeKey 194)) := by decide +kernel
lemma certificate194 : Certificate 194 := by
  refine ⟨data194,?_,?_⟩
  · rw [← src_eq194,← dst_eq194]
    exact valid194
  · decide +kernel

def src195 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,18,44,46,8,20,58,32,44,10,46,22,34,58]
def dst195 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,18,44,46,6,20,58,32,44,8,46,22,34,58,10]
def cycle195_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle195_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle195_2 : CycleData E W := ⟨2,![4,27,20,26],![8,10,46,44]⟩
def cycle195_3 : CycleData E W := ⟨3,![5,31,23,10,11],![2,10,58,20,18]⟩
def cycle195_4 : CycleData E W := ⟨2,![12,24,30,16],![4,32,58,34]⟩
def cycle195_5 : CycleData E W := ⟨3,![13,25,19,18,14],![16,32,44,18,30]⟩
def cycle195_6 : CycleData E W := ⟨3,![17,15,29,28,21],![6,30,34,22,46]⟩
def data195 : PartitionData E W := ⟨7,![cycle195_0,cycle195_1,cycle195_2,cycle195_3,cycle195_4,cycle195_5,cycle195_6]⟩
lemma valid195 : data195.Valid src195 dst195 Finset.univ := by decide +kernel
lemma src_eq195 : src195 = src (unkey (representativeKey 195)) := by decide +kernel
lemma dst_eq195 : dst195 = dst (unkey (representativeKey 195)) := by decide +kernel
lemma certificate195 : Certificate 195 := by
  refine ⟨data195,?_,?_⟩
  · rw [← src_eq195,← dst_eq195]
    exact valid195
  · decide +kernel

def src196 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,18,44,46,8,20,58,44,32,10,34,58,22,46]
def dst196 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,18,44,46,6,20,58,44,32,8,34,58,22,46,10]
def cycle196_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle196_1 : CycleData E W := ⟨3,![1,16,28,23,9],![3,4,34,58,20]⟩
def cycle196_2 : CycleData E W := ⟨3,![2,17,14,7,8],![3,6,30,16,22]⟩
def cycle196_3 : CycleData E W := ⟨2,![3,4,31,21],![6,8,10,46]⟩
def cycle196_4 : CycleData E W := ⟨3,![5,27,15,18,11],![2,10,34,30,18]⟩
def cycle196_5 : CycleData E W := ⟨3,![22,10,19,25,26],![8,20,18,44,32]⟩
def cycle196_6 : CycleData E W := ⟨2,![29,24,20,30],![22,58,44,46]⟩
def data196 : PartitionData E W := ⟨7,![cycle196_0,cycle196_1,cycle196_2,cycle196_3,cycle196_4,cycle196_5,cycle196_6]⟩
lemma valid196 : data196.Valid src196 dst196 Finset.univ := by decide +kernel
lemma src_eq196 : src196 = src (unkey (representativeKey 196)) := by decide +kernel
lemma dst_eq196 : dst196 = dst (unkey (representativeKey 196)) := by decide +kernel
lemma certificate196 : Certificate 196 := by
  refine ⟨data196,?_,?_⟩
  · rw [← src_eq196,← dst_eq196]
    exact valid196
  · decide +kernel

def src197 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,18,44,46,8,20,58,44,32,10,46,22,34,58]
def dst197 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,18,44,46,6,20,58,44,32,8,46,22,34,58,10]
def cycle197_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle197_1 : CycleData E W := ⟨2,![1,16,29,8],![3,4,34,22]⟩
def cycle197_2 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle197_3 : CycleData E W := ⟨4,![5,4,26,25,19,11],![2,10,8,32,44,18]⟩
def cycle197_4 : CycleData E W := ⟨3,![17,14,7,28,21],![6,30,16,22,46]⟩
def cycle197_5 : CycleData E W := ⟨3,![10,23,30,15,18],![18,20,58,34,30]⟩
def cycle197_6 : CycleData E W := ⟨2,![27,20,24,31],![10,46,44,58]⟩
def data197 : PartitionData E W := ⟨7,![cycle197_0,cycle197_1,cycle197_2,cycle197_3,cycle197_4,cycle197_5,cycle197_6]⟩
lemma valid197 : data197.Valid src197 dst197 Finset.univ := by decide +kernel
lemma src_eq197 : src197 = src (unkey (representativeKey 197)) := by decide +kernel
lemma dst_eq197 : dst197 = dst (unkey (representativeKey 197)) := by decide +kernel
lemma certificate197 : Certificate 197 := by
  refine ⟨data197,?_,?_⟩
  · rw [← src_eq197,← dst_eq197]
    exact valid197
  · decide +kernel

def src198 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,32,58,44,10,22,58,34,46]
def dst198 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,32,58,44,8,22,58,34,46,10]
def cycle198_0 : CycleData E W := ⟨3,![0,1,8,7,6],![2,4,3,22,16]⟩
def cycle198_1 : CycleData E W := ⟨2,![2,3,22,9],![3,6,8,20]⟩
def cycle198_2 : CycleData E W := ⟨3,![4,27,28,25,26],![8,10,22,58,44]⟩
def cycle198_3 : CycleData E W := ⟨2,![5,31,20,11],![2,10,46,18]⟩
def cycle198_4 : CycleData E W := ⟨4,![13,23,10,19,18,14],![16,32,20,18,44,30]⟩
def cycle198_5 : CycleData E W := ⟨2,![12,24,29,16],![4,32,58,34]⟩
def cycle198_6 : CycleData E W := ⟨2,![17,15,30,21],![6,30,34,46]⟩
def data198 : PartitionData E W := ⟨7,![cycle198_0,cycle198_1,cycle198_2,cycle198_3,cycle198_4,cycle198_5,cycle198_6]⟩
lemma valid198 : data198.Valid src198 dst198 Finset.univ := by decide +kernel
lemma src_eq198 : src198 = src (unkey (representativeKey 198)) := by decide +kernel
lemma dst_eq198 : dst198 = dst (unkey (representativeKey 198)) := by decide +kernel
lemma certificate198 : Certificate 198 := by
  refine ⟨data198,?_,?_⟩
  · rw [← src_eq198,← dst_eq198]
    exact valid198
  · decide +kernel

def src199 : E → W := ![2,4,3,6,8,10,2,16,22,3,20,18,4,32,16,30,34,6,30,44,18,46,8,20,32,58,44,10,22,58,46,34]
def dst199 : E → W := ![4,3,6,8,10,2,16,22,3,20,18,2,32,16,30,34,4,30,44,18,46,6,20,32,58,44,8,22,58,46,34,10]
def cycle199_0 : CycleData E W := ⟨2,![0,12,13,6],![2,4,32,16]⟩
def cycle199_1 : CycleData E W := ⟨3,![1,16,30,21,2],![3,4,34,46,6]⟩
def cycle199_2 : CycleData E W := ⟨2,![3,26,18,17],![6,8,44,30]⟩
def cycle199_3 : CycleData E W := ⟨3,![5,4,22,10,11],![2,10,8,20,18]⟩
def cycle199_4 : CycleData E W := ⟨3,![27,7,14,15,31],![10,22,16,30,34]⟩
def cycle199_5 : CycleData E W := ⟨3,![8,28,24,23,9],![3,22,58,32,20]⟩
def cycle199_6 : CycleData E W := ⟨2,![19,25,29,20],![18,44,58,46]⟩
def data199 : PartitionData E W := ⟨7,![cycle199_0,cycle199_1,cycle199_2,cycle199_3,cycle199_4,cycle199_5,cycle199_6]⟩
lemma valid199 : data199.Valid src199 dst199 Finset.univ := by decide +kernel
lemma src_eq199 : src199 = src (unkey (representativeKey 199)) := by decide +kernel
lemma dst_eq199 : dst199 = dst (unkey (representativeKey 199)) := by decide +kernel
lemma certificate199 : Certificate 199 := by
  refine ⟨data199,?_,?_⟩
  · rw [← src_eq199,← dst_eq199]
    exact valid199
  · decide +kernel
#print axioms certificate199
end Erdos184Work.SixRepresentativeCertificates1

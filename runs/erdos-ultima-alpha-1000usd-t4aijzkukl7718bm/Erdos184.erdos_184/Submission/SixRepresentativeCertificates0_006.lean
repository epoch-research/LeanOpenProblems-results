import Submission.SixRepresentativeCertificates0Base
namespace Erdos184Work.SixRepresentativeCertificates0
open PureSixRowModel0 LabelKernel Erdos184Serial
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false

def src300 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,32,20,44,58,10,46,22,34,58]
def dst300 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,32,20,44,58,8,46,22,34,58,10]
def cycle300_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle300_1 : CycleData E W := ⟨2,![1,19,18,10],![4,6,46,30]⟩
def cycle300_2 : CycleData E W := ⟨4,![2,20,21,22,16,15],![6,8,32,20,44,18]⟩
def cycle300_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle300_4 : CycleData E W := ⟨3,![4,25,26,8,9],![2,10,46,22,20]⟩
def cycle300_5 : CycleData E W := ⟨2,![6,7,27,12],![16,18,22,34]⟩
def cycle300_6 : CycleData E W := ⟨2,![11,28,23,17],![30,34,58,44]⟩
def data300 : PartitionData E W := ⟨7,![cycle300_0,cycle300_1,cycle300_2,cycle300_3,cycle300_4,cycle300_5,cycle300_6]⟩
lemma valid300 : data300.Valid src300 dst300 Finset.univ := by decide +kernel
lemma src_eq300 : src300 = src (unkey (representativeKey 300)) := by decide +kernel
lemma dst_eq300 : dst300 = dst (unkey (representativeKey 300)) := by decide +kernel
lemma certificate300 : Certificate 300 := by
  refine ⟨data300,?_,?_⟩
  · rw [← src_eq300,← dst_eq300]
    exact valid300
  · decide +kernel

def src301 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,44,20,32,58,10,22,46,58,34]
def dst301 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,44,20,32,58,8,22,46,58,34,10]
def cycle301_0 : CycleData E W := ⟨13,![0,1,19,18,11,12,13,23,24,3,25,7,16,21,9],![2,4,6,46,30,34,16,32,58,8,10,22,18,44,20]⟩
def cycle301_1 : CycleData E W := ⟨13,![4,29,28,27,26,8,22,14,10,17,20,2,15,6,5],![2,10,34,58,46,22,20,32,4,30,44,8,6,18,16]⟩
def data301 : PartitionData E W := ⟨2,![cycle301_0,cycle301_1]⟩
lemma valid301 : data301.Valid src301 dst301 Finset.univ := by decide +kernel
lemma src_eq301 : src301 = src (unkey (representativeKey 301)) := by decide +kernel
lemma dst_eq301 : dst301 = dst (unkey (representativeKey 301)) := by decide +kernel
lemma certificate301 : Certificate 301 := by
  refine ⟨data301,?_,?_⟩
  · rw [← src_eq301,← dst_eq301]
    exact valid301
  · decide +kernel

def src302 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,44,20,32,58,10,22,58,46,34]
def dst302 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,44,20,32,58,8,22,58,46,34,10]
def cycle302_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle302_1 : CycleData E W := ⟨3,![1,15,16,17,10],![4,6,18,44,30]⟩
def cycle302_2 : CycleData E W := ⟨2,![2,24,27,19],![6,8,58,46]⟩
def cycle302_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,10,8,44,20]⟩
def cycle302_4 : CycleData E W := ⟨3,![25,7,6,12,29],![10,22,18,16,34]⟩
def cycle302_5 : CycleData E W := ⟨2,![8,26,23,22],![20,22,58,32]⟩
def cycle302_6 : CycleData E W := ⟨1,![11,28,18],![30,34,46]⟩
def data302 : PartitionData E W := ⟨7,![cycle302_0,cycle302_1,cycle302_2,cycle302_3,cycle302_4,cycle302_5,cycle302_6]⟩
lemma valid302 : data302.Valid src302 dst302 Finset.univ := by decide +kernel
lemma src_eq302 : src302 = src (unkey (representativeKey 302)) := by decide +kernel
lemma dst_eq302 : dst302 = dst (unkey (representativeKey 302)) := by decide +kernel
lemma certificate302 : Certificate 302 := by
  refine ⟨data302,?_,?_⟩
  · rw [← src_eq302,← dst_eq302]
    exact valid302
  · decide +kernel

def src303 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,30,46,8,44,20,32,58,10,34,58,22,46]
def dst303 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,30,46,6,44,20,32,58,8,34,58,22,46,10]
def cycle303_0 : CycleData E W := ⟨13,![4,25,11,18,19,1,14,23,24,20,21,8,7,6,5],![2,10,34,30,46,6,4,32,58,8,44,20,22,18,16]⟩
def cycle303_1 : CycleData E W := ⟨13,![0,10,17,16,15,2,3,29,28,27,26,12,13,22,9],![2,4,30,44,18,6,8,10,46,22,58,34,16,32,20]⟩
def data303 : PartitionData E W := ⟨2,![cycle303_0,cycle303_1]⟩
lemma valid303 : data303.Valid src303 dst303 Finset.univ := by decide +kernel
lemma src_eq303 : src303 = src (unkey (representativeKey 303)) := by decide +kernel
lemma dst_eq303 : dst303 = dst (unkey (representativeKey 303)) := by decide +kernel
lemma certificate303 : Certificate 303 := by
  refine ⟨data303,?_,?_⟩
  · rw [← src_eq303,← dst_eq303]
    exact valid303
  · decide +kernel

def src304 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,20,32,44,58,10,34,58,22,46]
def dst304 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,20,32,44,58,8,34,58,22,46,10]
def cycle304_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle304_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle304_2 : CycleData E W := ⟨3,![2,24,23,16,15],![6,8,58,44,18]⟩
def cycle304_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle304_4 : CycleData E W := ⟨3,![6,7,27,26,12],![16,18,22,58,34]⟩
def cycle304_5 : CycleData E W := ⟨3,![8,28,17,22,21],![20,22,46,44,32]⟩
def cycle304_6 : CycleData E W := ⟨2,![25,11,18,29],![10,34,30,46]⟩
def data304 : PartitionData E W := ⟨7,![cycle304_0,cycle304_1,cycle304_2,cycle304_3,cycle304_4,cycle304_5,cycle304_6]⟩
lemma valid304 : data304.Valid src304 dst304 Finset.univ := by decide +kernel
lemma src_eq304 : src304 = src (unkey (representativeKey 304)) := by decide +kernel
lemma dst_eq304 : dst304 = dst (unkey (representativeKey 304)) := by decide +kernel
lemma certificate304 : Certificate 304 := by
  refine ⟨data304,?_,?_⟩
  · rw [← src_eq304,← dst_eq304]
    exact valid304
  · decide +kernel

def src305 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,20,32,44,58,10,46,22,34,58]
def dst305 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,20,32,44,58,8,46,22,34,58,10]
def cycle305_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle305_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle305_2 : CycleData E W := ⟨3,![2,20,8,7,15],![6,8,20,22,18]⟩
def cycle305_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle305_4 : CycleData E W := ⟨4,![4,25,17,22,21,9],![2,10,46,44,32,20]⟩
def cycle305_5 : CycleData E W := ⟨3,![6,16,23,28,12],![16,18,44,58,34]⟩
def cycle305_6 : CycleData E W := ⟨2,![26,18,11,27],![22,46,30,34]⟩
def data305 : PartitionData E W := ⟨7,![cycle305_0,cycle305_1,cycle305_2,cycle305_3,cycle305_4,cycle305_5,cycle305_6]⟩
lemma valid305 : data305.Valid src305 dst305 Finset.univ := by decide +kernel
lemma src_eq305 : src305 = src (unkey (representativeKey 305)) := by decide +kernel
lemma dst_eq305 : dst305 = dst (unkey (representativeKey 305)) := by decide +kernel
lemma certificate305 : Certificate 305 := by
  refine ⟨data305,?_,?_⟩
  · rw [← src_eq305,← dst_eq305]
    exact valid305
  · decide +kernel

def src306 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,20,44,32,58,10,34,58,22,46]
def dst306 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,20,44,32,58,8,34,58,22,46,10]
def cycle306_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle306_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle306_2 : CycleData E W := ⟨4,![2,24,23,22,16,15],![6,8,58,32,44,18]⟩
def cycle306_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle306_4 : CycleData E W := ⟨3,![6,7,27,26,12],![16,18,22,58,34]⟩
def cycle306_5 : CycleData E W := ⟨2,![8,28,17,21],![20,22,46,44]⟩
def cycle306_6 : CycleData E W := ⟨2,![25,11,18,29],![10,34,30,46]⟩
def data306 : PartitionData E W := ⟨7,![cycle306_0,cycle306_1,cycle306_2,cycle306_3,cycle306_4,cycle306_5,cycle306_6]⟩
lemma valid306 : data306.Valid src306 dst306 Finset.univ := by decide +kernel
lemma src_eq306 : src306 = src (unkey (representativeKey 306)) := by decide +kernel
lemma dst_eq306 : dst306 = dst (unkey (representativeKey 306)) := by decide +kernel
lemma certificate306 : Certificate 306 := by
  refine ⟨data306,?_,?_⟩
  · rw [← src_eq306,← dst_eq306]
    exact valid306
  · decide +kernel

def src307 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,20,58,32,44,10,34,22,58,46]
def dst307 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,20,58,32,44,8,34,22,58,46,10]
def cycle307_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle307_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle307_2 : CycleData E W := ⟨2,![2,24,16,15],![6,8,44,18]⟩
def cycle307_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle307_4 : CycleData E W := ⟨2,![6,7,26,12],![16,18,22,34]⟩
def cycle307_5 : CycleData E W := ⟨1,![8,27,21],![20,22,58]⟩
def cycle307_6 : CycleData E W := ⟨2,![25,11,18,29],![10,34,30,46]⟩
def cycle307_7 : CycleData E W := ⟨2,![22,28,17,23],![32,58,46,44]⟩
def data307 : PartitionData E W := ⟨8,![cycle307_0,cycle307_1,cycle307_2,cycle307_3,cycle307_4,cycle307_5,cycle307_6,cycle307_7]⟩
lemma valid307 : data307.Valid src307 dst307 Finset.univ := by decide +kernel
lemma src_eq307 : src307 = src (unkey (representativeKey 307)) := by decide +kernel
lemma dst_eq307 : dst307 = dst (unkey (representativeKey 307)) := by decide +kernel
lemma certificate307 : Certificate 307 := by
  refine ⟨data307,?_,?_⟩
  · rw [← src_eq307,← dst_eq307]
    exact valid307
  · decide +kernel

def src308 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,20,58,32,44,10,34,58,22,46]
def dst308 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,20,58,32,44,8,34,58,22,46,10]
def cycle308_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle308_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle308_2 : CycleData E W := ⟨2,![2,24,16,15],![6,8,44,18]⟩
def cycle308_3 : CycleData E W := ⟨2,![4,3,20,9],![2,10,8,20]⟩
def cycle308_4 : CycleData E W := ⟨4,![6,7,8,21,26,12],![16,18,22,20,58,34]⟩
def cycle308_5 : CycleData E W := ⟨2,![25,11,18,29],![10,34,30,46]⟩
def cycle308_6 : CycleData E W := ⟨3,![27,22,23,17,28],![22,58,32,44,46]⟩
def data308 : PartitionData E W := ⟨7,![cycle308_0,cycle308_1,cycle308_2,cycle308_3,cycle308_4,cycle308_5,cycle308_6]⟩
lemma valid308 : data308.Valid src308 dst308 Finset.univ := by decide +kernel
lemma src_eq308 : src308 = src (unkey (representativeKey 308)) := by decide +kernel
lemma dst_eq308 : dst308 = dst (unkey (representativeKey 308)) := by decide +kernel
lemma certificate308 : Certificate 308 := by
  refine ⟨data308,?_,?_⟩
  · rw [← src_eq308,← dst_eq308]
    exact valid308
  · decide +kernel

def src309 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,32,20,44,58,10,34,58,22,46]
def dst309 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,32,20,44,58,8,34,58,22,46,10]
def cycle309_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle309_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle309_2 : CycleData E W := ⟨3,![2,24,23,16,15],![6,8,58,44,18]⟩
def cycle309_3 : CycleData E W := ⟨3,![4,3,20,21,9],![2,10,8,32,20]⟩
def cycle309_4 : CycleData E W := ⟨3,![6,7,27,26,12],![16,18,22,58,34]⟩
def cycle309_5 : CycleData E W := ⟨2,![8,28,17,22],![20,22,46,44]⟩
def cycle309_6 : CycleData E W := ⟨2,![25,11,18,29],![10,34,30,46]⟩
def data309 : PartitionData E W := ⟨7,![cycle309_0,cycle309_1,cycle309_2,cycle309_3,cycle309_4,cycle309_5,cycle309_6]⟩
lemma valid309 : data309.Valid src309 dst309 Finset.univ := by decide +kernel
lemma src_eq309 : src309 = src (unkey (representativeKey 309)) := by decide +kernel
lemma dst_eq309 : dst309 = dst (unkey (representativeKey 309)) := by decide +kernel
lemma certificate309 : Certificate 309 := by
  refine ⟨data309,?_,?_⟩
  · rw [← src_eq309,← dst_eq309]
    exact valid309
  · decide +kernel

def src310 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,32,20,44,58,10,46,22,34,58]
def dst310 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,32,20,44,58,8,46,22,34,58,10]
def cycle310_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle310_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle310_2 : CycleData E W := ⟨4,![2,20,21,8,7,15],![6,8,32,20,22,18]⟩
def cycle310_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle310_4 : CycleData E W := ⟨3,![4,25,17,22,9],![2,10,46,44,20]⟩
def cycle310_5 : CycleData E W := ⟨3,![6,16,23,28,12],![16,18,44,58,34]⟩
def cycle310_6 : CycleData E W := ⟨2,![26,18,11,27],![22,46,30,34]⟩
def data310 : PartitionData E W := ⟨7,![cycle310_0,cycle310_1,cycle310_2,cycle310_3,cycle310_4,cycle310_5,cycle310_6]⟩
lemma valid310 : data310.Valid src310 dst310 Finset.univ := by decide +kernel
lemma src_eq310 : src310 = src (unkey (representativeKey 310)) := by decide +kernel
lemma dst_eq310 : dst310 = dst (unkey (representativeKey 310)) := by decide +kernel
lemma certificate310 : Certificate 310 := by
  refine ⟨data310,?_,?_⟩
  · rw [← src_eq310,← dst_eq310]
    exact valid310
  · decide +kernel

def src311 : E → W := ![2,4,6,8,10,2,16,18,22,20,4,30,34,16,32,6,18,44,46,30,8,44,20,32,58,10,34,58,22,46]
def dst311 : E → W := ![4,6,8,10,2,16,18,22,20,2,30,34,16,32,4,18,44,46,30,6,44,20,32,58,8,34,58,22,46,10]
def cycle311_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,32,16]⟩
def cycle311_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle311_2 : CycleData E W := ⟨2,![2,20,16,15],![6,8,44,18]⟩
def cycle311_3 : CycleData E W := ⟨4,![4,3,24,23,22,9],![2,10,8,58,32,20]⟩
def cycle311_4 : CycleData E W := ⟨3,![6,7,27,26,12],![16,18,22,58,34]⟩
def cycle311_5 : CycleData E W := ⟨2,![8,28,17,21],![20,22,46,44]⟩
def cycle311_6 : CycleData E W := ⟨2,![25,11,18,29],![10,34,30,46]⟩
def data311 : PartitionData E W := ⟨7,![cycle311_0,cycle311_1,cycle311_2,cycle311_3,cycle311_4,cycle311_5,cycle311_6]⟩
lemma valid311 : data311.Valid src311 dst311 Finset.univ := by decide +kernel
lemma src_eq311 : src311 = src (unkey (representativeKey 311)) := by decide +kernel
lemma dst_eq311 : dst311 = dst (unkey (representativeKey 311)) := by decide +kernel
lemma certificate311 : Certificate 311 := by
  refine ⟨data311,?_,?_⟩
  · rw [← src_eq311,← dst_eq311]
    exact valid311
  · decide +kernel

def src312 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,30,44,8,20,32,44,58,10,34,22,58,46]
def dst312 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,30,44,6,20,32,44,58,8,34,22,58,46,10]
def cycle312_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle312_1 : CycleData E W := ⟨3,![1,15,7,21,14],![4,6,18,20,32]⟩
def cycle312_2 : CycleData E W := ⟨2,![2,24,23,19],![6,8,58,44]⟩
def cycle312_3 : CycleData E W := ⟨4,![3,29,17,11,6,20],![8,10,46,30,16,20]⟩
def cycle312_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle312_5 : CycleData E W := ⟨2,![8,27,28,16],![18,22,58,46]⟩
def cycle312_6 : CycleData E W := ⟨2,![12,13,22,18],![30,34,32,44]⟩
def data312 : PartitionData E W := ⟨7,![cycle312_0,cycle312_1,cycle312_2,cycle312_3,cycle312_4,cycle312_5,cycle312_6]⟩
lemma valid312 : data312.Valid src312 dst312 Finset.univ := by decide +kernel
lemma src_eq312 : src312 = src (unkey (representativeKey 312)) := by decide +kernel
lemma dst_eq312 : dst312 = dst (unkey (representativeKey 312)) := by decide +kernel
lemma certificate312 : Certificate 312 := by
  refine ⟨data312,?_,?_⟩
  · rw [← src_eq312,← dst_eq312]
    exact valid312
  · decide +kernel

def src313 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,30,44,8,20,32,44,58,10,34,58,22,46]
def dst313 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,30,44,6,20,32,44,58,8,34,58,22,46,10]
def cycle313_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle313_1 : CycleData E W := ⟨3,![1,15,7,21,14],![4,6,18,20,32]⟩
def cycle313_2 : CycleData E W := ⟨4,![2,20,6,11,18,19],![6,8,20,16,30,44]⟩
def cycle313_3 : CycleData E W := ⟨3,![4,3,24,27,9],![2,10,8,58,22]⟩
def cycle313_4 : CycleData E W := ⟨1,![8,28,16],![18,22,46]⟩
def cycle313_5 : CycleData E W := ⟨2,![25,12,17,29],![10,34,30,46]⟩
def cycle313_6 : CycleData E W := ⟨2,![13,26,23,22],![32,34,58,44]⟩
def data313 : PartitionData E W := ⟨7,![cycle313_0,cycle313_1,cycle313_2,cycle313_3,cycle313_4,cycle313_5,cycle313_6]⟩
lemma valid313 : data313.Valid src313 dst313 Finset.univ := by decide +kernel
lemma src_eq313 : src313 = src (unkey (representativeKey 313)) := by decide +kernel
lemma dst_eq313 : dst313 = dst (unkey (representativeKey 313)) := by decide +kernel
lemma certificate313 : Certificate 313 := by
  refine ⟨data313,?_,?_⟩
  · rw [← src_eq313,← dst_eq313]
    exact valid313
  · decide +kernel

def src314 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,30,44,8,20,32,44,58,10,46,34,22,58]
def dst314 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,30,44,6,20,32,44,58,8,46,34,22,58,10]
def cycle314_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle314_1 : CycleData E W := ⟨3,![1,15,7,21,14],![4,6,18,20,32]⟩
def cycle314_2 : CycleData E W := ⟨4,![2,20,6,11,18,19],![6,8,20,16,30,44]⟩
def cycle314_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle314_4 : CycleData E W := ⟨3,![4,25,16,8,9],![2,10,46,18,22]⟩
def cycle314_5 : CycleData E W := ⟨1,![12,26,17],![30,34,46]⟩
def cycle314_6 : CycleData E W := ⟨3,![27,13,22,23,28],![22,34,32,44,58]⟩
def data314 : PartitionData E W := ⟨7,![cycle314_0,cycle314_1,cycle314_2,cycle314_3,cycle314_4,cycle314_5,cycle314_6]⟩
lemma valid314 : data314.Valid src314 dst314 Finset.univ := by decide +kernel
lemma src_eq314 : src314 = src (unkey (representativeKey 314)) := by decide +kernel
lemma dst_eq314 : dst314 = dst (unkey (representativeKey 314)) := by decide +kernel
lemma certificate314 : Certificate 314 := by
  refine ⟨data314,?_,?_⟩
  · rw [← src_eq314,← dst_eq314]
    exact valid314
  · decide +kernel

def src315 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,30,44,8,32,58,20,44,10,34,22,58,46]
def dst315 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,30,44,6,32,58,20,44,8,34,22,58,46,10]
def cycle315_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle315_1 : CycleData E W := ⟨5,![1,15,16,17,12,13,14],![4,6,18,46,30,34,32]⟩
def cycle315_2 : CycleData E W := ⟨1,![2,24,19],![6,8,44]⟩
def cycle315_3 : CycleData E W := ⟨3,![3,29,28,21,20],![8,10,46,58,32]⟩
def cycle315_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle315_5 : CycleData E W := ⟨2,![6,23,18,11],![16,20,44,30]⟩
def cycle315_6 : CycleData E W := ⟨2,![7,22,27,8],![18,20,58,22]⟩
def data315 : PartitionData E W := ⟨7,![cycle315_0,cycle315_1,cycle315_2,cycle315_3,cycle315_4,cycle315_5,cycle315_6]⟩
lemma valid315 : data315.Valid src315 dst315 Finset.univ := by decide +kernel
lemma src_eq315 : src315 = src (unkey (representativeKey 315)) := by decide +kernel
lemma dst_eq315 : dst315 = dst (unkey (representativeKey 315)) := by decide +kernel
lemma certificate315 : Certificate 315 := by
  refine ⟨data315,?_,?_⟩
  · rw [← src_eq315,← dst_eq315]
    exact valid315
  · decide +kernel

def src316 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,30,44,8,32,58,20,44,10,46,34,22,58]
def dst316 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,30,44,6,32,58,20,44,8,46,34,22,58,10]
def cycle316_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle316_1 : CycleData E W := ⟨5,![1,15,16,17,12,13,14],![4,6,18,46,30,34,32]⟩
def cycle316_2 : CycleData E W := ⟨1,![2,24,19],![6,8,44]⟩
def cycle316_3 : CycleData E W := ⟨2,![3,29,21,20],![8,10,58,32]⟩
def cycle316_4 : CycleData E W := ⟨3,![4,25,26,27,9],![2,10,46,34,22]⟩
def cycle316_5 : CycleData E W := ⟨2,![6,23,18,11],![16,20,44,30]⟩
def cycle316_6 : CycleData E W := ⟨2,![7,22,28,8],![18,20,58,22]⟩
def data316 : PartitionData E W := ⟨7,![cycle316_0,cycle316_1,cycle316_2,cycle316_3,cycle316_4,cycle316_5,cycle316_6]⟩
lemma valid316 : data316.Valid src316 dst316 Finset.univ := by decide +kernel
lemma src_eq316 : src316 = src (unkey (representativeKey 316)) := by decide +kernel
lemma dst_eq316 : dst316 = dst (unkey (representativeKey 316)) := by decide +kernel
lemma certificate316 : Certificate 316 := by
  refine ⟨data316,?_,?_⟩
  · rw [← src_eq316,← dst_eq316]
    exact valid316
  · decide +kernel

def src317 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,30,44,8,44,20,32,58,10,34,22,58,46]
def dst317 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,30,44,6,44,20,32,58,8,34,22,58,46,10]
def cycle317_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle317_1 : CycleData E W := ⟨5,![1,15,16,17,12,13,14],![4,6,18,46,30,34,32]⟩
def cycle317_2 : CycleData E W := ⟨1,![2,20,19],![6,8,44]⟩
def cycle317_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle317_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle317_5 : CycleData E W := ⟨2,![6,21,18,11],![16,20,44,30]⟩
def cycle317_6 : CycleData E W := ⟨3,![7,22,23,27,8],![18,20,32,58,22]⟩
def data317 : PartitionData E W := ⟨7,![cycle317_0,cycle317_1,cycle317_2,cycle317_3,cycle317_4,cycle317_5,cycle317_6]⟩
lemma valid317 : data317.Valid src317 dst317 Finset.univ := by decide +kernel
lemma src_eq317 : src317 = src (unkey (representativeKey 317)) := by decide +kernel
lemma dst_eq317 : dst317 = dst (unkey (representativeKey 317)) := by decide +kernel
lemma certificate317 : Certificate 317 := by
  refine ⟨data317,?_,?_⟩
  · rw [← src_eq317,← dst_eq317]
    exact valid317
  · decide +kernel

def src318 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,20,32,44,58,10,22,58,34,46]
def dst318 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,20,32,44,58,8,22,58,34,46,10]
def cycle318_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle318_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle318_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle318_3 : CycleData E W := ⟨3,![4,3,24,26,9],![2,10,8,58,22]⟩
def cycle318_4 : CycleData E W := ⟨3,![6,21,22,18,11],![16,20,32,44,30]⟩
def cycle318_5 : CycleData E W := ⟨2,![25,8,16,29],![10,22,18,46]⟩
def cycle318_6 : CycleData E W := ⟨2,![27,23,17,28],![34,58,44,46]⟩
def data318 : PartitionData E W := ⟨7,![cycle318_0,cycle318_1,cycle318_2,cycle318_3,cycle318_4,cycle318_5,cycle318_6]⟩
lemma valid318 : data318.Valid src318 dst318 Finset.univ := by decide +kernel
lemma src_eq318 : src318 = src (unkey (representativeKey 318)) := by decide +kernel
lemma dst_eq318 : dst318 = dst (unkey (representativeKey 318)) := by decide +kernel
lemma certificate318 : Certificate 318 := by
  refine ⟨data318,?_,?_⟩
  · rw [← src_eq318,← dst_eq318]
    exact valid318
  · decide +kernel

def src319 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,20,32,44,58,10,34,22,58,46]
def dst319 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,20,32,44,58,8,34,22,58,46,10]
def cycle319_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle319_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle319_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle319_3 : CycleData E W := ⟨3,![4,3,24,27,9],![2,10,8,58,22]⟩
def cycle319_4 : CycleData E W := ⟨3,![6,21,22,18,11],![16,20,32,44,30]⟩
def cycle319_5 : CycleData E W := ⟨3,![25,26,8,16,29],![10,34,22,18,46]⟩
def cycle319_6 : CycleData E W := ⟨1,![17,28,23],![44,46,58]⟩
def data319 : PartitionData E W := ⟨7,![cycle319_0,cycle319_1,cycle319_2,cycle319_3,cycle319_4,cycle319_5,cycle319_6]⟩
lemma valid319 : data319.Valid src319 dst319 Finset.univ := by decide +kernel
lemma src_eq319 : src319 = src (unkey (representativeKey 319)) := by decide +kernel
lemma dst_eq319 : dst319 = dst (unkey (representativeKey 319)) := by decide +kernel
lemma certificate319 : Certificate 319 := by
  refine ⟨data319,?_,?_⟩
  · rw [← src_eq319,← dst_eq319]
    exact valid319
  · decide +kernel

def src320 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,20,32,44,58,10,34,58,22,46]
def dst320 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,20,32,44,58,8,34,58,22,46,10]
def cycle320_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle320_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle320_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle320_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle320_4 : CycleData E W := ⟨3,![4,29,16,8,9],![2,10,46,18,22]⟩
def cycle320_5 : CycleData E W := ⟨3,![6,21,22,18,11],![16,20,32,44,30]⟩
def cycle320_6 : CycleData E W := ⟨2,![27,23,17,28],![22,58,44,46]⟩
def data320 : PartitionData E W := ⟨7,![cycle320_0,cycle320_1,cycle320_2,cycle320_3,cycle320_4,cycle320_5,cycle320_6]⟩
lemma valid320 : data320.Valid src320 dst320 Finset.univ := by decide +kernel
lemma src_eq320 : src320 = src (unkey (representativeKey 320)) := by decide +kernel
lemma dst_eq320 : dst320 = dst (unkey (representativeKey 320)) := by decide +kernel
lemma certificate320 : Certificate 320 := by
  refine ⟨data320,?_,?_⟩
  · rw [← src_eq320,← dst_eq320]
    exact valid320
  · decide +kernel

def src321 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,32,58,20,44,10,34,22,58,46]
def dst321 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,32,58,20,44,8,34,22,58,46,10]
def cycle321_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle321_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle321_2 : CycleData E W := ⟨4,![2,20,21,22,7,15],![6,8,32,58,20,18]⟩
def cycle321_3 : CycleData E W := ⟨2,![3,29,17,24],![8,10,46,44]⟩
def cycle321_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle321_5 : CycleData E W := ⟨2,![6,23,18,11],![16,20,44,30]⟩
def cycle321_6 : CycleData E W := ⟨2,![8,27,28,16],![18,22,58,46]⟩
def data321 : PartitionData E W := ⟨7,![cycle321_0,cycle321_1,cycle321_2,cycle321_3,cycle321_4,cycle321_5,cycle321_6]⟩
lemma valid321 : data321.Valid src321 dst321 Finset.univ := by decide +kernel
lemma src_eq321 : src321 = src (unkey (representativeKey 321)) := by decide +kernel
lemma dst_eq321 : dst321 = dst (unkey (representativeKey 321)) := by decide +kernel
lemma certificate321 : Certificate 321 := by
  refine ⟨data321,?_,?_⟩
  · rw [← src_eq321,← dst_eq321]
    exact valid321
  · decide +kernel

def src322 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,32,58,20,44,10,46,34,22,58]
def dst322 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,32,58,20,44,8,46,34,22,58,10]
def cycle322_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle322_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle322_2 : CycleData E W := ⟨4,![2,20,21,22,7,15],![6,8,32,58,20,18]⟩
def cycle322_3 : CycleData E W := ⟨2,![3,25,17,24],![8,10,46,44]⟩
def cycle322_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle322_5 : CycleData E W := ⟨2,![6,23,18,11],![16,20,44,30]⟩
def cycle322_6 : CycleData E W := ⟨2,![8,27,26,16],![18,22,34,46]⟩
def data322 : PartitionData E W := ⟨7,![cycle322_0,cycle322_1,cycle322_2,cycle322_3,cycle322_4,cycle322_5,cycle322_6]⟩
lemma valid322 : data322.Valid src322 dst322 Finset.univ := by decide +kernel
lemma src_eq322 : src322 = src (unkey (representativeKey 322)) := by decide +kernel
lemma dst_eq322 : dst322 = dst (unkey (representativeKey 322)) := by decide +kernel
lemma certificate322 : Certificate 322 := by
  refine ⟨data322,?_,?_⟩
  · rw [← src_eq322,← dst_eq322]
    exact valid322
  · decide +kernel

def src323 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,44,20,32,58,10,22,58,34,46]
def dst323 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,44,20,32,58,8,22,58,34,46,10]
def cycle323_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle323_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle323_2 : CycleData E W := ⟨3,![2,20,17,16,15],![6,8,44,46,18]⟩
def cycle323_3 : CycleData E W := ⟨3,![3,29,28,27,24],![8,10,46,34,58]⟩
def cycle323_4 : CycleData E W := ⟨1,![4,25,9],![2,10,22]⟩
def cycle323_5 : CycleData E W := ⟨2,![6,21,18,11],![16,20,44,30]⟩
def cycle323_6 : CycleData E W := ⟨3,![7,22,23,26,8],![18,20,32,58,22]⟩
def data323 : PartitionData E W := ⟨7,![cycle323_0,cycle323_1,cycle323_2,cycle323_3,cycle323_4,cycle323_5,cycle323_6]⟩
lemma valid323 : data323.Valid src323 dst323 Finset.univ := by decide +kernel
lemma src_eq323 : src323 = src (unkey (representativeKey 323)) := by decide +kernel
lemma dst_eq323 : dst323 = dst (unkey (representativeKey 323)) := by decide +kernel
lemma certificate323 : Certificate 323 := by
  refine ⟨data323,?_,?_⟩
  · rw [← src_eq323,← dst_eq323]
    exact valid323
  · decide +kernel

def src324 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,44,20,32,58,10,34,22,58,46]
def dst324 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,44,20,32,58,8,34,22,58,46,10]
def cycle324_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle324_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle324_2 : CycleData E W := ⟨3,![2,20,17,16,15],![6,8,44,46,18]⟩
def cycle324_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle324_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle324_5 : CycleData E W := ⟨2,![6,21,18,11],![16,20,44,30]⟩
def cycle324_6 : CycleData E W := ⟨3,![7,22,23,27,8],![18,20,32,58,22]⟩
def data324 : PartitionData E W := ⟨7,![cycle324_0,cycle324_1,cycle324_2,cycle324_3,cycle324_4,cycle324_5,cycle324_6]⟩
lemma valid324 : data324.Valid src324 dst324 Finset.univ := by decide +kernel
lemma src_eq324 : src324 = src (unkey (representativeKey 324)) := by decide +kernel
lemma dst_eq324 : dst324 = dst (unkey (representativeKey 324)) := by decide +kernel
lemma certificate324 : Certificate 324 := by
  refine ⟨data324,?_,?_⟩
  · rw [← src_eq324,← dst_eq324]
    exact valid324
  · decide +kernel

def src325 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,18,46,44,30,8,44,20,32,58,10,34,58,22,46]
def dst325 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,18,46,44,30,6,44,20,32,58,8,34,58,22,46,10]
def cycle325_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle325_1 : CycleData E W := ⟨3,![1,19,12,13,14],![4,6,30,34,32]⟩
def cycle325_2 : CycleData E W := ⟨3,![2,20,17,16,15],![6,8,44,46,18]⟩
def cycle325_3 : CycleData E W := ⟨2,![3,25,26,24],![8,10,34,58]⟩
def cycle325_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle325_5 : CycleData E W := ⟨2,![6,21,18,11],![16,20,44,30]⟩
def cycle325_6 : CycleData E W := ⟨3,![7,22,23,27,8],![18,20,32,58,22]⟩
def data325 : PartitionData E W := ⟨7,![cycle325_0,cycle325_1,cycle325_2,cycle325_3,cycle325_4,cycle325_5,cycle325_6]⟩
lemma valid325 : data325.Valid src325 dst325 Finset.univ := by decide +kernel
lemma src_eq325 : src325 = src (unkey (representativeKey 325)) := by decide +kernel
lemma dst_eq325 : dst325 = dst (unkey (representativeKey 325)) := by decide +kernel
lemma certificate325 : Certificate 325 := by
  refine ⟨data325,?_,?_⟩
  · rw [← src_eq325,← dst_eq325]
    exact valid325
  · decide +kernel

def src326 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,30,34,32,6,30,46,18,44,8,44,20,32,58,10,34,22,58,46]
def dst326 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,30,34,32,4,30,46,18,44,6,44,20,32,58,8,34,22,58,46,10]
def cycle326_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle326_1 : CycleData E W := ⟨3,![1,15,12,13,14],![4,6,30,34,32]⟩
def cycle326_2 : CycleData E W := ⟨1,![2,20,19],![6,8,44]⟩
def cycle326_3 : CycleData E W := ⟨3,![4,3,24,27,9],![2,10,8,58,22]⟩
def cycle326_4 : CycleData E W := ⟨4,![6,22,23,28,16,11],![16,20,32,58,46,30]⟩
def cycle326_5 : CycleData E W := ⟨1,![7,21,18],![18,20,44]⟩
def cycle326_6 : CycleData E W := ⟨3,![25,26,8,17,29],![10,34,22,18,46]⟩
def data326 : PartitionData E W := ⟨7,![cycle326_0,cycle326_1,cycle326_2,cycle326_3,cycle326_4,cycle326_5,cycle326_6]⟩
lemma valid326 : data326.Valid src326 dst326 Finset.univ := by decide +kernel
lemma src_eq326 : src326 = src (unkey (representativeKey 326)) := by decide +kernel
lemma dst_eq326 : dst326 = dst (unkey (representativeKey 326)) := by decide +kernel
lemma certificate326 : Certificate 326 := by
  refine ⟨data326,?_,?_⟩
  · rw [← src_eq326,← dst_eq326]
    exact valid326
  · decide +kernel

def src327 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,32,34,30,6,18,30,44,46,8,20,44,32,58,10,34,22,58,46]
def dst327 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,32,34,30,4,18,30,44,46,6,20,44,32,58,8,34,22,58,46,10]
def cycle327_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle327_1 : CycleData E W := ⟨2,![1,15,16,14],![4,6,18,30]⟩
def cycle327_2 : CycleData E W := ⟨3,![2,20,21,18,19],![6,8,20,44,46]⟩
def cycle327_3 : CycleData E W := ⟨2,![3,29,28,24],![8,10,46,58]⟩
def cycle327_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle327_5 : CycleData E W := ⟨4,![6,7,8,27,23,11],![16,20,18,22,58,32]⟩
def cycle327_6 : CycleData E W := ⟨2,![13,12,22,17],![30,34,32,44]⟩
def data327 : PartitionData E W := ⟨7,![cycle327_0,cycle327_1,cycle327_2,cycle327_3,cycle327_4,cycle327_5,cycle327_6]⟩
lemma valid327 : data327.Valid src327 dst327 Finset.univ := by decide +kernel
lemma src_eq327 : src327 = src (unkey (representativeKey 327)) := by decide +kernel
lemma dst_eq327 : dst327 = dst (unkey (representativeKey 327)) := by decide +kernel
lemma certificate327 : Certificate 327 := by
  refine ⟨data327,?_,?_⟩
  · rw [← src_eq327,← dst_eq327]
    exact valid327
  · decide +kernel

def src328 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,32,34,30,6,18,30,44,46,8,20,44,32,58,10,34,46,22,58]
def dst328 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,32,34,30,4,18,30,44,46,6,20,44,32,58,8,34,46,22,58,10]
def cycle328_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle328_1 : CycleData E W := ⟨2,![1,15,16,14],![4,6,18,30]⟩
def cycle328_2 : CycleData E W := ⟨3,![2,20,21,18,19],![6,8,20,44,46]⟩
def cycle328_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle328_4 : CycleData E W := ⟨3,![4,25,26,27,9],![2,10,34,46,22]⟩
def cycle328_5 : CycleData E W := ⟨4,![6,7,8,28,23,11],![16,20,18,22,58,32]⟩
def cycle328_6 : CycleData E W := ⟨2,![13,12,22,17],![30,34,32,44]⟩
def data328 : PartitionData E W := ⟨7,![cycle328_0,cycle328_1,cycle328_2,cycle328_3,cycle328_4,cycle328_5,cycle328_6]⟩
lemma valid328 : data328.Valid src328 dst328 Finset.univ := by decide +kernel
lemma src_eq328 : src328 = src (unkey (representativeKey 328)) := by decide +kernel
lemma dst_eq328 : dst328 = dst (unkey (representativeKey 328)) := by decide +kernel
lemma certificate328 : Certificate 328 := by
  refine ⟨data328,?_,?_⟩
  · rw [← src_eq328,← dst_eq328]
    exact valid328
  · decide +kernel

def src329 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,32,34,30,6,18,30,44,46,8,20,58,44,32,10,22,46,34,58]
def dst329 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,32,34,30,4,18,30,44,46,6,20,58,44,32,8,22,46,34,58,10]
def cycle329_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle329_1 : CycleData E W := ⟨2,![1,15,16,14],![4,6,18,30]⟩
def cycle329_2 : CycleData E W := ⟨3,![2,24,23,18,19],![6,8,32,44,46]⟩
def cycle329_3 : CycleData E W := ⟨2,![3,29,21,20],![8,10,58,20]⟩
def cycle329_4 : CycleData E W := ⟨1,![4,25,9],![2,10,22]⟩
def cycle329_5 : CycleData E W := ⟨5,![6,7,8,26,27,12,11],![16,20,18,22,46,34,32]⟩
def cycle329_6 : CycleData E W := ⟨2,![13,28,22,17],![30,34,58,44]⟩
def data329 : PartitionData E W := ⟨7,![cycle329_0,cycle329_1,cycle329_2,cycle329_3,cycle329_4,cycle329_5,cycle329_6]⟩
lemma valid329 : data329.Valid src329 dst329 Finset.univ := by decide +kernel
lemma src_eq329 : src329 = src (unkey (representativeKey 329)) := by decide +kernel
lemma dst_eq329 : dst329 = dst (unkey (representativeKey 329)) := by decide +kernel
lemma certificate329 : Certificate 329 := by
  refine ⟨data329,?_,?_⟩
  · rw [← src_eq329,← dst_eq329]
    exact valid329
  · decide +kernel

def src330 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,32,34,30,6,18,30,44,46,8,20,58,44,32,10,34,22,58,46]
def dst330 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,32,34,30,4,18,30,44,46,6,20,58,44,32,8,34,22,58,46,10]
def cycle330_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle330_1 : CycleData E W := ⟨2,![1,15,16,14],![4,6,18,30]⟩
def cycle330_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle330_3 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle330_4 : CycleData E W := ⟨2,![20,6,11,24],![8,20,16,32]⟩
def cycle330_5 : CycleData E W := ⟨2,![7,21,27,8],![18,20,58,22]⟩
def cycle330_6 : CycleData E W := ⟨2,![13,12,23,17],![30,34,32,44]⟩
def cycle330_7 : CycleData E W := ⟨1,![18,28,22],![44,46,58]⟩
def data330 : PartitionData E W := ⟨8,![cycle330_0,cycle330_1,cycle330_2,cycle330_3,cycle330_4,cycle330_5,cycle330_6,cycle330_7]⟩
lemma valid330 : data330.Valid src330 dst330 Finset.univ := by decide +kernel
lemma src_eq330 : src330 = src (unkey (representativeKey 330)) := by decide +kernel
lemma dst_eq330 : dst330 = dst (unkey (representativeKey 330)) := by decide +kernel
lemma certificate330 : Certificate 330 := by
  refine ⟨data330,?_,?_⟩
  · rw [← src_eq330,← dst_eq330]
    exact valid330
  · decide +kernel

def src331 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,16,32,34,30,6,18,46,30,44,8,32,58,20,44,10,46,22,34,58]
def dst331 : E → W := ![4,6,8,10,2,16,20,18,22,2,16,32,34,30,4,18,46,30,44,6,32,58,20,44,8,46,22,34,58,10]
def cycle331_0 : CycleData E W := ⟨1,![0,10,5],![2,4,16]⟩
def cycle331_1 : CycleData E W := ⟨3,![1,15,16,17,14],![4,6,18,46,30]⟩
def cycle331_2 : CycleData E W := ⟨1,![2,24,19],![6,8,44]⟩
def cycle331_3 : CycleData E W := ⟨2,![3,29,21,20],![8,10,58,32]⟩
def cycle331_4 : CycleData E W := ⟨2,![4,25,26,9],![2,10,46,22]⟩
def cycle331_5 : CycleData E W := ⟨4,![6,23,18,13,12,11],![16,20,44,30,34,32]⟩
def cycle331_6 : CycleData E W := ⟨3,![7,22,28,27,8],![18,20,58,34,22]⟩
def data331 : PartitionData E W := ⟨7,![cycle331_0,cycle331_1,cycle331_2,cycle331_3,cycle331_4,cycle331_5,cycle331_6]⟩
lemma valid331 : data331.Valid src331 dst331 Finset.univ := by decide +kernel
lemma src_eq331 : src331 = src (unkey (representativeKey 331)) := by decide +kernel
lemma dst_eq331 : dst331 = dst (unkey (representativeKey 331)) := by decide +kernel
lemma certificate331 : Certificate 331 := by
  refine ⟨data331,?_,?_⟩
  · rw [← src_eq331,← dst_eq331]
    exact valid331
  · decide +kernel

def src332 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,30,44,46,8,20,58,44,32,10,46,22,34,58]
def dst332 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,30,44,46,6,20,58,44,32,8,46,22,34,58,10]
def cycle332_0 : CycleData E W := ⟨13,![4,25,18,22,21,20,2,1,14,13,12,11,16,8,9],![2,10,46,44,58,20,8,6,4,34,32,16,30,18,22]⟩
def cycle332_1 : CycleData E W := ⟨13,![0,10,17,23,24,3,29,28,27,26,19,15,7,6,5],![2,4,30,44,32,8,10,58,34,22,46,6,18,20,16]⟩
def data332 : PartitionData E W := ⟨2,![cycle332_0,cycle332_1]⟩
lemma valid332 : data332.Valid src332 dst332 Finset.univ := by decide +kernel
lemma src_eq332 : src332 = src (unkey (representativeKey 332)) := by decide +kernel
lemma dst_eq332 : dst332 = dst (unkey (representativeKey 332)) := by decide +kernel
lemma certificate332 : Certificate 332 := by
  refine ⟨data332,?_,?_⟩
  · rw [← src_eq332,← dst_eq332]
    exact valid332
  · decide +kernel

def src333 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,30,44,46,8,20,58,44,32,10,46,34,22,58]
def dst333 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,30,44,46,6,20,58,44,32,8,46,34,22,58,10]
def cycle333_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle333_1 : CycleData E W := ⟨3,![1,15,8,27,14],![4,6,18,22,34]⟩
def cycle333_2 : CycleData E W := ⟨2,![2,3,25,19],![6,8,10,46]⟩
def cycle333_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle333_4 : CycleData E W := ⟨2,![20,6,12,24],![8,20,16,32]⟩
def cycle333_5 : CycleData E W := ⟨3,![7,21,22,17,16],![18,20,58,44,30]⟩
def cycle333_6 : CycleData E W := ⟨2,![13,26,18,23],![32,34,46,44]⟩
def data333 : PartitionData E W := ⟨7,![cycle333_0,cycle333_1,cycle333_2,cycle333_3,cycle333_4,cycle333_5,cycle333_6]⟩
lemma valid333 : data333.Valid src333 dst333 Finset.univ := by decide +kernel
lemma src_eq333 : src333 = src (unkey (representativeKey 333)) := by decide +kernel
lemma dst_eq333 : dst333 = dst (unkey (representativeKey 333)) := by decide +kernel
lemma certificate333 : Certificate 333 := by
  refine ⟨data333,?_,?_⟩
  · rw [← src_eq333,← dst_eq333]
    exact valid333
  · decide +kernel

def src334 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,30,44,46,8,32,58,20,44,10,46,22,34,58]
def dst334 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,30,44,46,6,32,58,20,44,8,46,22,34,58,10]
def cycle334_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle334_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle334_2 : CycleData E W := ⟨2,![3,25,18,24],![8,10,46,44]⟩
def cycle334_3 : CycleData E W := ⟨3,![4,29,28,27,9],![2,10,58,34,22]⟩
def cycle334_4 : CycleData E W := ⟨2,![6,22,21,12],![16,20,58,32]⟩
def cycle334_5 : CycleData E W := ⟨2,![7,23,17,16],![18,20,44,30]⟩
def cycle334_6 : CycleData E W := ⟨2,![15,8,26,19],![6,18,22,46]⟩
def data334 : PartitionData E W := ⟨7,![cycle334_0,cycle334_1,cycle334_2,cycle334_3,cycle334_4,cycle334_5,cycle334_6]⟩
lemma valid334 : data334.Valid src334 dst334 Finset.univ := by decide +kernel
lemma src_eq334 : src334 = src (unkey (representativeKey 334)) := by decide +kernel
lemma dst_eq334 : dst334 = dst (unkey (representativeKey 334)) := by decide +kernel
lemma certificate334 : Certificate 334 := by
  refine ⟨data334,?_,?_⟩
  · rw [← src_eq334,← dst_eq334]
    exact valid334
  · decide +kernel

def src335 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,30,44,46,8,32,58,20,44,10,46,34,22,58]
def dst335 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,30,44,46,6,32,58,20,44,8,46,34,22,58,10]
def cycle335_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle335_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle335_2 : CycleData E W := ⟨2,![3,25,18,24],![8,10,46,44]⟩
def cycle335_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle335_4 : CycleData E W := ⟨2,![6,22,21,12],![16,20,58,32]⟩
def cycle335_5 : CycleData E W := ⟨2,![7,23,17,16],![18,20,44,30]⟩
def cycle335_6 : CycleData E W := ⟨3,![15,8,27,26,19],![6,18,22,34,46]⟩
def data335 : PartitionData E W := ⟨7,![cycle335_0,cycle335_1,cycle335_2,cycle335_3,cycle335_4,cycle335_5,cycle335_6]⟩
lemma valid335 : data335.Valid src335 dst335 Finset.univ := by decide +kernel
lemma src_eq335 : src335 = src (unkey (representativeKey 335)) := by decide +kernel
lemma dst_eq335 : dst335 = dst (unkey (representativeKey 335)) := by decide +kernel
lemma certificate335 : Certificate 335 := by
  refine ⟨data335,?_,?_⟩
  · rw [← src_eq335,← dst_eq335]
    exact valid335
  · decide +kernel

def src336 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,44,46,30,8,20,32,44,58,10,46,34,22,58]
def dst336 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,44,46,30,6,20,32,44,58,8,46,34,22,58,10]
def cycle336_0 : CycleData E W := ⟨2,![0,14,27,9],![2,4,34,22]⟩
def cycle336_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle336_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle336_3 : CycleData E W := ⟨1,![3,29,24],![8,10,58]⟩
def cycle336_4 : CycleData E W := ⟨3,![4,25,18,11,5],![2,10,46,30,16]⟩
def cycle336_5 : CycleData E W := ⟨1,![6,21,12],![16,20,32]⟩
def cycle336_6 : CycleData E W := ⟨2,![8,28,23,16],![18,22,58,44]⟩
def cycle336_7 : CycleData E W := ⟨2,![13,26,17,22],![32,34,46,44]⟩
def data336 : PartitionData E W := ⟨8,![cycle336_0,cycle336_1,cycle336_2,cycle336_3,cycle336_4,cycle336_5,cycle336_6,cycle336_7]⟩
lemma valid336 : data336.Valid src336 dst336 Finset.univ := by decide +kernel
lemma src_eq336 : src336 = src (unkey (representativeKey 336)) := by decide +kernel
lemma dst_eq336 : dst336 = dst (unkey (representativeKey 336)) := by decide +kernel
lemma certificate336 : Certificate 336 := by
  refine ⟨data336,?_,?_⟩
  · rw [← src_eq336,← dst_eq336]
    exact valid336
  · decide +kernel

def src337 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,44,46,30,8,20,58,44,32,10,46,22,34,58]
def dst337 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,44,46,30,6,20,58,44,32,8,46,22,34,58,10]
def cycle337_0 : CycleData E W := ⟨2,![0,14,27,9],![2,4,34,22]⟩
def cycle337_1 : CycleData E W := ⟨1,![1,19,10],![4,6,30]⟩
def cycle337_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle337_3 : CycleData E W := ⟨3,![4,3,24,12,5],![2,10,8,32,16]⟩
def cycle337_4 : CycleData E W := ⟨4,![25,18,11,6,21,29],![10,46,30,16,20,58]⟩
def cycle337_5 : CycleData E W := ⟨2,![8,26,17,16],![18,22,46,44]⟩
def cycle337_6 : CycleData E W := ⟨2,![13,28,22,23],![32,34,58,44]⟩
def data337 : PartitionData E W := ⟨7,![cycle337_0,cycle337_1,cycle337_2,cycle337_3,cycle337_4,cycle337_5,cycle337_6]⟩
lemma valid337 : data337.Valid src337 dst337 Finset.univ := by decide +kernel
lemma src_eq337 : src337 = src (unkey (representativeKey 337)) := by decide +kernel
lemma dst_eq337 : dst337 = dst (unkey (representativeKey 337)) := by decide +kernel
lemma certificate337 : Certificate 337 := by
  refine ⟨data337,?_,?_⟩
  · rw [← src_eq337,← dst_eq337]
    exact valid337
  · decide +kernel

def src338 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,44,46,30,8,20,58,44,32,10,46,34,22,58]
def dst338 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,44,46,30,6,20,58,44,32,8,46,34,22,58,10]
def cycle338_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle338_1 : CycleData E W := ⟨3,![1,15,8,27,14],![4,6,18,22,34]⟩
def cycle338_2 : CycleData E W := ⟨3,![2,3,25,18,19],![6,8,10,46,30]⟩
def cycle338_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle338_4 : CycleData E W := ⟨2,![20,6,12,24],![8,20,16,32]⟩
def cycle338_5 : CycleData E W := ⟨2,![7,21,22,16],![18,20,58,44]⟩
def cycle338_6 : CycleData E W := ⟨2,![13,26,17,23],![32,34,46,44]⟩
def data338 : PartitionData E W := ⟨7,![cycle338_0,cycle338_1,cycle338_2,cycle338_3,cycle338_4,cycle338_5,cycle338_6]⟩
lemma valid338 : data338.Valid src338 dst338 Finset.univ := by decide +kernel
lemma src_eq338 : src338 = src (unkey (representativeKey 338)) := by decide +kernel
lemma dst_eq338 : dst338 = dst (unkey (representativeKey 338)) := by decide +kernel
lemma certificate338 : Certificate 338 := by
  refine ⟨data338,?_,?_⟩
  · rw [← src_eq338,← dst_eq338]
    exact valid338
  · decide +kernel

def src339 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,44,46,30,8,32,58,20,44,10,46,22,34,58]
def dst339 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,44,46,30,6,32,58,20,44,8,46,22,34,58,10]
def cycle339_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle339_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle339_2 : CycleData E W := ⟨2,![3,25,17,24],![8,10,46,44]⟩
def cycle339_3 : CycleData E W := ⟨3,![4,29,28,27,9],![2,10,58,34,22]⟩
def cycle339_4 : CycleData E W := ⟨2,![6,22,21,12],![16,20,58,32]⟩
def cycle339_5 : CycleData E W := ⟨1,![7,23,16],![18,20,44]⟩
def cycle339_6 : CycleData E W := ⟨3,![15,8,26,18,19],![6,18,22,46,30]⟩
def data339 : PartitionData E W := ⟨7,![cycle339_0,cycle339_1,cycle339_2,cycle339_3,cycle339_4,cycle339_5,cycle339_6]⟩
lemma valid339 : data339.Valid src339 dst339 Finset.univ := by decide +kernel
lemma src_eq339 : src339 = src (unkey (representativeKey 339)) := by decide +kernel
lemma dst_eq339 : dst339 = dst (unkey (representativeKey 339)) := by decide +kernel
lemma certificate339 : Certificate 339 := by
  refine ⟨data339,?_,?_⟩
  · rw [← src_eq339,← dst_eq339]
    exact valid339
  · decide +kernel

def src340 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,44,46,30,8,32,58,20,44,10,46,34,22,58]
def dst340 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,44,46,30,6,32,58,20,44,8,46,34,22,58,10]
def cycle340_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle340_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle340_2 : CycleData E W := ⟨2,![3,25,17,24],![8,10,46,44]⟩
def cycle340_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle340_4 : CycleData E W := ⟨2,![6,22,21,12],![16,20,58,32]⟩
def cycle340_5 : CycleData E W := ⟨1,![7,23,16],![18,20,44]⟩
def cycle340_6 : CycleData E W := ⟨4,![15,8,27,26,18,19],![6,18,22,34,46,30]⟩
def data340 : PartitionData E W := ⟨7,![cycle340_0,cycle340_1,cycle340_2,cycle340_3,cycle340_4,cycle340_5,cycle340_6]⟩
lemma valid340 : data340.Valid src340 dst340 Finset.univ := by decide +kernel
lemma src_eq340 : src340 = src (unkey (representativeKey 340)) := by decide +kernel
lemma dst_eq340 : dst340 = dst (unkey (representativeKey 340)) := by decide +kernel
lemma certificate340 : Certificate 340 := by
  refine ⟨data340,?_,?_⟩
  · rw [← src_eq340,← dst_eq340]
    exact valid340
  · decide +kernel

def src341 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,46,30,44,8,20,32,44,58,10,46,34,22,58]
def dst341 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,46,30,44,6,20,32,44,58,8,46,34,22,58,10]
def cycle341_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle341_1 : CycleData E W := ⟨3,![1,19,22,13,14],![4,6,44,32,34]⟩
def cycle341_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle341_3 : CycleData E W := ⟨4,![3,25,17,18,23,24],![8,10,46,30,44,58]⟩
def cycle341_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle341_5 : CycleData E W := ⟨1,![6,21,12],![16,20,32]⟩
def cycle341_6 : CycleData E W := ⟨2,![8,27,26,16],![18,22,34,46]⟩
def data341 : PartitionData E W := ⟨7,![cycle341_0,cycle341_1,cycle341_2,cycle341_3,cycle341_4,cycle341_5,cycle341_6]⟩
lemma valid341 : data341.Valid src341 dst341 Finset.univ := by decide +kernel
lemma src_eq341 : src341 = src (unkey (representativeKey 341)) := by decide +kernel
lemma dst_eq341 : dst341 = dst (unkey (representativeKey 341)) := by decide +kernel
lemma certificate341 : Certificate 341 := by
  refine ⟨data341,?_,?_⟩
  · rw [← src_eq341,← dst_eq341]
    exact valid341
  · decide +kernel

def src342 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,46,30,44,8,20,58,44,32,10,46,34,22,58]
def dst342 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,46,30,44,6,20,58,44,32,8,46,34,22,58,10]
def cycle342_0 : CycleData E W := ⟨13,![5,12,13,14,1,2,3,25,17,18,22,21,7,8,9],![2,16,32,34,4,6,8,10,46,30,44,58,20,18,22]⟩
def cycle342_1 : CycleData E W := ⟨13,![0,10,11,6,20,24,23,19,15,16,26,27,28,29,4],![2,4,30,16,20,8,32,44,6,18,46,34,22,58,10]⟩
def data342 : PartitionData E W := ⟨2,![cycle342_0,cycle342_1]⟩
lemma valid342 : data342.Valid src342 dst342 Finset.univ := by decide +kernel
lemma src_eq342 : src342 = src (unkey (representativeKey 342)) := by decide +kernel
lemma dst_eq342 : dst342 = dst (unkey (representativeKey 342)) := by decide +kernel
lemma certificate342 : Certificate 342 := by
  refine ⟨data342,?_,?_⟩
  · rw [← src_eq342,← dst_eq342]
    exact valid342
  · decide +kernel

def src343 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,46,30,44,8,32,58,20,44,10,46,34,22,58]
def dst343 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,46,30,44,6,32,58,20,44,8,46,34,22,58,10]
def cycle343_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle343_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle343_2 : CycleData E W := ⟨3,![3,25,17,18,24],![8,10,46,30,44]⟩
def cycle343_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle343_4 : CycleData E W := ⟨2,![6,22,21,12],![16,20,58,32]⟩
def cycle343_5 : CycleData E W := ⟨2,![15,7,23,19],![6,18,20,44]⟩
def cycle343_6 : CycleData E W := ⟨2,![8,27,26,16],![18,22,34,46]⟩
def data343 : PartitionData E W := ⟨7,![cycle343_0,cycle343_1,cycle343_2,cycle343_3,cycle343_4,cycle343_5,cycle343_6]⟩
lemma valid343 : data343.Valid src343 dst343 Finset.univ := by decide +kernel
lemma src_eq343 : src343 = src (unkey (representativeKey 343)) := by decide +kernel
lemma dst_eq343 : dst343 = dst (unkey (representativeKey 343)) := by decide +kernel
lemma certificate343 : Certificate 343 := by
  refine ⟨data343,?_,?_⟩
  · rw [← src_eq343,← dst_eq343]
    exact valid343
  · decide +kernel

def src344 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,46,44,30,8,20,32,44,58,10,46,34,22,58]
def dst344 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,46,44,30,6,20,32,44,58,8,46,34,22,58,10]
def cycle344_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle344_1 : CycleData E W := ⟨4,![1,19,18,22,13,14],![4,6,30,44,32,34]⟩
def cycle344_2 : CycleData E W := ⟨2,![2,20,7,15],![6,8,20,18]⟩
def cycle344_3 : CycleData E W := ⟨3,![3,25,17,23,24],![8,10,46,44,58]⟩
def cycle344_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle344_5 : CycleData E W := ⟨1,![6,21,12],![16,20,32]⟩
def cycle344_6 : CycleData E W := ⟨2,![8,27,26,16],![18,22,34,46]⟩
def data344 : PartitionData E W := ⟨7,![cycle344_0,cycle344_1,cycle344_2,cycle344_3,cycle344_4,cycle344_5,cycle344_6]⟩
lemma valid344 : data344.Valid src344 dst344 Finset.univ := by decide +kernel
lemma src_eq344 : src344 = src (unkey (representativeKey 344)) := by decide +kernel
lemma dst_eq344 : dst344 = dst (unkey (representativeKey 344)) := by decide +kernel
lemma certificate344 : Certificate 344 := by
  refine ⟨data344,?_,?_⟩
  · rw [← src_eq344,← dst_eq344]
    exact valid344
  · decide +kernel

def src345 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,46,44,30,8,32,58,20,44,10,46,22,34,58]
def dst345 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,46,44,30,6,32,58,20,44,8,46,22,34,58,10]
def cycle345_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle345_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle345_2 : CycleData E W := ⟨2,![3,25,17,24],![8,10,46,44]⟩
def cycle345_3 : CycleData E W := ⟨3,![4,29,28,27,9],![2,10,58,34,22]⟩
def cycle345_4 : CycleData E W := ⟨2,![6,22,21,12],![16,20,58,32]⟩
def cycle345_5 : CycleData E W := ⟨3,![15,7,23,18,19],![6,18,20,44,30]⟩
def cycle345_6 : CycleData E W := ⟨1,![8,26,16],![18,22,46]⟩
def data345 : PartitionData E W := ⟨7,![cycle345_0,cycle345_1,cycle345_2,cycle345_3,cycle345_4,cycle345_5,cycle345_6]⟩
lemma valid345 : data345.Valid src345 dst345 Finset.univ := by decide +kernel
lemma src_eq345 : src345 = src (unkey (representativeKey 345)) := by decide +kernel
lemma dst_eq345 : dst345 = dst (unkey (representativeKey 345)) := by decide +kernel
lemma certificate345 : Certificate 345 := by
  refine ⟨data345,?_,?_⟩
  · rw [← src_eq345,← dst_eq345]
    exact valid345
  · decide +kernel

def src346 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,32,34,6,18,46,44,30,8,32,58,20,44,10,46,34,22,58]
def dst346 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,32,34,4,18,46,44,30,6,32,58,20,44,8,46,34,22,58,10]
def cycle346_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle346_1 : CycleData E W := ⟨3,![1,2,20,13,14],![4,6,8,32,34]⟩
def cycle346_2 : CycleData E W := ⟨2,![3,25,17,24],![8,10,46,44]⟩
def cycle346_3 : CycleData E W := ⟨2,![4,29,28,9],![2,10,58,22]⟩
def cycle346_4 : CycleData E W := ⟨2,![6,22,21,12],![16,20,58,32]⟩
def cycle346_5 : CycleData E W := ⟨3,![15,7,23,18,19],![6,18,20,44,30]⟩
def cycle346_6 : CycleData E W := ⟨2,![8,27,26,16],![18,22,34,46]⟩
def data346 : PartitionData E W := ⟨7,![cycle346_0,cycle346_1,cycle346_2,cycle346_3,cycle346_4,cycle346_5,cycle346_6]⟩
lemma valid346 : data346.Valid src346 dst346 Finset.univ := by decide +kernel
lemma src_eq346 : src346 = src (unkey (representativeKey 346)) := by decide +kernel
lemma dst_eq346 : dst346 = dst (unkey (representativeKey 346)) := by decide +kernel
lemma certificate346 : Certificate 346 := by
  refine ⟨data346,?_,?_⟩
  · rw [← src_eq346,← dst_eq346]
    exact valid346
  · decide +kernel

def src347 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,30,44,46,8,20,32,58,44,10,34,58,22,46]
def dst347 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,30,44,46,6,20,32,58,44,8,34,58,22,46,10]
def cycle347_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,30,16]⟩
def cycle347_1 : CycleData E W := ⟨3,![1,15,7,21,14],![4,6,18,20,32]⟩
def cycle347_2 : CycleData E W := ⟨2,![2,24,18,19],![6,8,44,46]⟩
def cycle347_3 : CycleData E W := ⟨3,![3,25,12,6,20],![8,10,34,16,20]⟩
def cycle347_4 : CycleData E W := ⟨2,![4,29,28,9],![2,10,46,22]⟩
def cycle347_5 : CycleData E W := ⟨3,![8,27,23,17,16],![18,22,58,44,30]⟩
def cycle347_6 : CycleData E W := ⟨1,![13,26,22],![32,34,58]⟩
def data347 : PartitionData E W := ⟨7,![cycle347_0,cycle347_1,cycle347_2,cycle347_3,cycle347_4,cycle347_5,cycle347_6]⟩
lemma valid347 : data347.Valid src347 dst347 Finset.univ := by decide +kernel
lemma src_eq347 : src347 = src (unkey (representativeKey 347)) := by decide +kernel
lemma dst_eq347 : dst347 = dst (unkey (representativeKey 347)) := by decide +kernel
lemma certificate347 : Certificate 347 := by
  refine ⟨data347,?_,?_⟩
  · rw [← src_eq347,← dst_eq347]
    exact valid347
  · decide +kernel

def src348 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,30,44,46,8,20,32,58,44,10,46,34,22,58]
def dst348 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,30,44,46,6,20,32,58,44,8,46,34,22,58,10]
def cycle348_0 : CycleData E W := ⟨13,![4,25,18,23,22,13,12,6,20,2,1,10,16,8,9],![2,10,46,44,58,32,34,16,20,8,6,4,30,18,22]⟩
def cycle348_1 : CycleData E W := ⟨13,![0,14,21,7,15,19,26,27,28,29,3,24,17,11,5],![2,4,32,20,18,6,46,34,22,58,10,8,44,30,16]⟩
def data348 : PartitionData E W := ⟨2,![cycle348_0,cycle348_1]⟩
lemma valid348 : data348.Valid src348 dst348 Finset.univ := by decide +kernel
lemma src_eq348 : src348 = src (unkey (representativeKey 348)) := by decide +kernel
lemma dst_eq348 : dst348 = dst (unkey (representativeKey 348)) := by decide +kernel
lemma certificate348 : Certificate 348 := by
  refine ⟨data348,?_,?_⟩
  · rw [← src_eq348,← dst_eq348]
    exact valid348
  · decide +kernel

def src349 : E → W := ![2,4,6,8,10,2,16,20,18,22,4,30,16,34,32,6,18,30,44,46,8,20,44,32,58,10,34,22,58,46]
def dst349 : E → W := ![4,6,8,10,2,16,20,18,22,2,30,16,34,32,4,18,30,44,46,6,20,44,32,58,8,34,22,58,46,10]
def cycle349_0 : CycleData E W := ⟨3,![0,14,13,12,5],![2,4,32,34,16]⟩
def cycle349_1 : CycleData E W := ⟨2,![1,15,16,10],![4,6,18,30]⟩
def cycle349_2 : CycleData E W := ⟨2,![2,3,29,19],![6,8,10,46]⟩
def cycle349_3 : CycleData E W := ⟨2,![4,25,26,9],![2,10,34,22]⟩
def cycle349_4 : CycleData E W := ⟨2,![6,21,17,11],![16,20,44,30]⟩
def cycle349_5 : CycleData E W := ⟨3,![20,7,8,27,24],![8,20,18,22,58]⟩
def cycle349_6 : CycleData E W := ⟨2,![22,18,28,23],![32,44,46,58]⟩
def data349 : PartitionData E W := ⟨7,![cycle349_0,cycle349_1,cycle349_2,cycle349_3,cycle349_4,cycle349_5,cycle349_6]⟩
lemma valid349 : data349.Valid src349 dst349 Finset.univ := by decide +kernel
lemma src_eq349 : src349 = src (unkey (representativeKey 349)) := by decide +kernel
lemma dst_eq349 : dst349 = dst (unkey (representativeKey 349)) := by decide +kernel
lemma certificate349 : Certificate 349 := by
  refine ⟨data349,?_,?_⟩
  · rw [← src_eq349,← dst_eq349]
    exact valid349
  · decide +kernel
#print axioms certificate349
end Erdos184Work.SixRepresentativeCertificates0

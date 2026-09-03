import Submission.LabelCycleCertificates



/-! The finite simple-cycle catalogue of the Petersen graph. -/

namespace Erdos184Work.PetersenBase

open Erdos184Serial LabelKernel

set_option maxHeartbeats 100000000

set_option maxRecDepth 100000

set_option Elab.async false

def src : Fin 15 → Fin 10 := ![0,0,0,1,1,2,2,3,3,4,5,5,6,6,7]

def dst : Fin 15 → Fin 10 := ![1,4,5,2,6,3,7,4,8,9,7,8,8,9,9]

def code : Code (Fin 15) := LabelKernel.code src dst

instance validDecidable (s : Finset (Fin 15)) : Decidable (code.valid s) := by
  unfold code LabelKernel.code LabelKernel.valid
  infer_instance

instance circuitDecidable (s : Finset (Fin 15)) : Decidable (Circuit code s) := by
  unfold Circuit
  infer_instance

def cycle0 : CycleData (Fin 15) (Fin 10) := ⟨3,![0,3,5,7,1],![0,1,2,3,4]⟩

lemma valid0 : cycle0.Valid src dst := by decide +kernel

def cycle1 : CycleData (Fin 15) (Fin 10) := ⟨3,![0,3,6,10,2],![0,1,2,7,5]⟩

lemma valid1 : cycle1.Valid src dst := by decide +kernel

def cycle2 : CycleData (Fin 15) (Fin 10) := ⟨3,![0,4,12,11,2],![0,1,6,8,5]⟩

lemma valid2 : cycle2.Valid src dst := by decide +kernel

def cycle3 : CycleData (Fin 15) (Fin 10) := ⟨3,![0,4,13,9,1],![0,1,6,9,4]⟩

lemma valid3 : cycle3.Valid src dst := by decide +kernel

def cycle4 : CycleData (Fin 15) (Fin 10) := ⟨3,![1,7,8,11,2],![0,4,3,8,5]⟩

lemma valid4 : cycle4.Valid src dst := by decide +kernel

def cycle5 : CycleData (Fin 15) (Fin 10) := ⟨3,![1,9,14,10,2],![0,4,9,7,5]⟩

lemma valid5 : cycle5.Valid src dst := by decide +kernel

def cycle6 : CycleData (Fin 15) (Fin 10) := ⟨3,![3,5,8,12,4],![1,2,3,8,6]⟩

lemma valid6 : cycle6.Valid src dst := by decide +kernel

def cycle7 : CycleData (Fin 15) (Fin 10) := ⟨3,![3,6,14,13,4],![1,2,7,9,6]⟩

lemma valid7 : cycle7.Valid src dst := by decide +kernel

def cycle8 : CycleData (Fin 15) (Fin 10) := ⟨3,![5,7,9,14,6],![2,3,4,9,7]⟩

lemma valid8 : cycle8.Valid src dst := by decide +kernel

def cycle9 : CycleData (Fin 15) (Fin 10) := ⟨3,![5,8,11,10,6],![2,3,8,5,7]⟩

lemma valid9 : cycle9.Valid src dst := by decide +kernel

def cycle10 : CycleData (Fin 15) (Fin 10) := ⟨3,![7,9,13,12,8],![3,4,9,6,8]⟩

lemma valid10 : cycle10.Valid src dst := by decide +kernel

def cycle11 : CycleData (Fin 15) (Fin 10) := ⟨3,![10,14,13,12,11],![5,7,9,6,8]⟩

lemma valid11 : cycle11.Valid src dst := by decide +kernel

def cycle12 : CycleData (Fin 15) (Fin 10) := ⟨4,![0,3,5,8,11,2],![0,1,2,3,8,5]⟩

lemma valid12 : cycle12.Valid src dst := by decide +kernel

def cycle13 : CycleData (Fin 15) (Fin 10) := ⟨4,![0,3,6,14,9,1],![0,1,2,7,9,4]⟩

lemma valid13 : cycle13.Valid src dst := by decide +kernel

def cycle14 : CycleData (Fin 15) (Fin 10) := ⟨4,![0,4,12,8,7,1],![0,1,6,8,3,4]⟩

lemma valid14 : cycle14.Valid src dst := by decide +kernel

def cycle15 : CycleData (Fin 15) (Fin 10) := ⟨4,![0,4,13,14,10,2],![0,1,6,9,7,5]⟩

lemma valid15 : cycle15.Valid src dst := by decide +kernel

def cycle16 : CycleData (Fin 15) (Fin 10) := ⟨4,![1,7,5,6,10,2],![0,4,3,2,7,5]⟩

lemma valid16 : cycle16.Valid src dst := by decide +kernel

def cycle17 : CycleData (Fin 15) (Fin 10) := ⟨4,![1,9,13,12,11,2],![0,4,9,6,8,5]⟩

lemma valid17 : cycle17.Valid src dst := by decide +kernel

def cycle18 : CycleData (Fin 15) (Fin 10) := ⟨4,![3,5,7,9,13,4],![1,2,3,4,9,6]⟩

lemma valid18 : cycle18.Valid src dst := by decide +kernel

def cycle19 : CycleData (Fin 15) (Fin 10) := ⟨4,![3,6,10,11,12,4],![1,2,7,5,8,6]⟩

lemma valid19 : cycle19.Valid src dst := by decide +kernel

def cycle20 : CycleData (Fin 15) (Fin 10) := ⟨4,![5,8,12,13,14,6],![2,3,8,6,9,7]⟩

lemma valid20 : cycle20.Valid src dst := by decide +kernel

def cycle21 : CycleData (Fin 15) (Fin 10) := ⟨4,![7,9,14,10,11,8],![3,4,9,7,5,8]⟩

lemma valid21 : cycle21.Valid src dst := by decide +kernel

def cycle22 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,3,5,7,9,14,10,2],![0,1,2,3,4,9,7,5]⟩

lemma valid22 : cycle22.Valid src dst := by decide +kernel

def cycle23 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,3,5,8,12,13,9,1],![0,1,2,3,8,6,9,4]⟩

lemma valid23 : cycle23.Valid src dst := by decide +kernel

def cycle24 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,3,6,10,11,8,7,1],![0,1,2,7,5,8,3,4]⟩

lemma valid24 : cycle24.Valid src dst := by decide +kernel

def cycle25 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,3,6,14,13,12,11,2],![0,1,2,7,9,6,8,5]⟩

lemma valid25 : cycle25.Valid src dst := by decide +kernel

def cycle26 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,4,12,8,5,6,10,2],![0,1,6,8,3,2,7,5]⟩

lemma valid26 : cycle26.Valid src dst := by decide +kernel

def cycle27 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,4,12,11,10,14,9,1],![0,1,6,8,5,7,9,4]⟩

lemma valid27 : cycle27.Valid src dst := by decide +kernel

def cycle28 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,4,13,9,7,8,11,2],![0,1,6,9,4,3,8,5]⟩

lemma valid28 : cycle28.Valid src dst := by decide +kernel

def cycle29 : CycleData (Fin 15) (Fin 10) := ⟨6,![0,4,13,14,6,5,7,1],![0,1,6,9,7,2,3,4]⟩

lemma valid29 : cycle29.Valid src dst := by decide +kernel

def cycle30 : CycleData (Fin 15) (Fin 10) := ⟨6,![1,7,5,3,4,12,11,2],![0,4,3,2,1,6,8,5]⟩

lemma valid30 : cycle30.Valid src dst := by decide +kernel

def cycle31 : CycleData (Fin 15) (Fin 10) := ⟨6,![1,7,8,12,13,14,10,2],![0,4,3,8,6,9,7,5]⟩

lemma valid31 : cycle31.Valid src dst := by decide +kernel

def cycle32 : CycleData (Fin 15) (Fin 10) := ⟨6,![1,9,13,4,3,6,10,2],![0,4,9,6,1,2,7,5]⟩

lemma valid32 : cycle32.Valid src dst := by decide +kernel

def cycle33 : CycleData (Fin 15) (Fin 10) := ⟨6,![1,9,14,6,5,8,11,2],![0,4,9,7,2,3,8,5]⟩

lemma valid33 : cycle33.Valid src dst := by decide +kernel

def cycle34 : CycleData (Fin 15) (Fin 10) := ⟨6,![3,5,8,11,10,14,13,4],![1,2,3,8,5,7,9,6]⟩

lemma valid34 : cycle34.Valid src dst := by decide +kernel

def cycle35 : CycleData (Fin 15) (Fin 10) := ⟨6,![3,6,14,9,7,8,12,4],![1,2,7,9,4,3,8,6]⟩

lemma valid35 : cycle35.Valid src dst := by decide +kernel

def cycle36 : CycleData (Fin 15) (Fin 10) := ⟨6,![5,7,9,13,12,11,10,6],![2,3,4,9,6,8,5,7]⟩

lemma valid36 : cycle36.Valid src dst := by decide +kernel

def cycle37 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,3,5,7,9,13,12,11,2],![0,1,2,3,4,9,6,8,5]⟩

lemma valid37 : cycle37.Valid src dst := by decide +kernel

def cycle38 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,3,5,8,11,10,14,9,1],![0,1,2,3,8,5,7,9,4]⟩

lemma valid38 : cycle38.Valid src dst := by decide +kernel

def cycle39 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,3,5,8,12,13,14,10,2],![0,1,2,3,8,6,9,7,5]⟩

lemma valid39 : cycle39.Valid src dst := by decide +kernel

def cycle40 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,3,6,10,11,12,13,9,1],![0,1,2,7,5,8,6,9,4]⟩

lemma valid40 : cycle40.Valid src dst := by decide +kernel

def cycle41 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,3,6,14,9,7,8,11,2],![0,1,2,7,9,4,3,8,5]⟩

lemma valid41 : cycle41.Valid src dst := by decide +kernel

def cycle42 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,3,6,14,13,12,8,7,1],![0,1,2,7,9,6,8,3,4]⟩

lemma valid42 : cycle42.Valid src dst := by decide +kernel

def cycle43 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,4,12,8,5,6,14,9,1],![0,1,6,8,3,2,7,9,4]⟩

lemma valid43 : cycle43.Valid src dst := by decide +kernel

def cycle44 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,4,12,8,7,9,14,10,2],![0,1,6,8,3,4,9,7,5]⟩

lemma valid44 : cycle44.Valid src dst := by decide +kernel

def cycle45 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,4,12,11,10,6,5,7,1],![0,1,6,8,5,7,2,3,4]⟩

lemma valid45 : cycle45.Valid src dst := by decide +kernel

def cycle46 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,4,13,9,7,5,6,10,2],![0,1,6,9,4,3,2,7,5]⟩

lemma valid46 : cycle46.Valid src dst := by decide +kernel

def cycle47 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,4,13,14,6,5,8,11,2],![0,1,6,9,7,2,3,8,5]⟩

lemma valid47 : cycle47.Valid src dst := by decide +kernel

def cycle48 : CycleData (Fin 15) (Fin 10) := ⟨7,![0,4,13,14,10,11,8,7,1],![0,1,6,9,7,5,8,3,4]⟩

lemma valid48 : cycle48.Valid src dst := by decide +kernel

def cycle49 : CycleData (Fin 15) (Fin 10) := ⟨7,![1,7,5,3,4,13,14,10,2],![0,4,3,2,1,6,9,7,5]⟩

lemma valid49 : cycle49.Valid src dst := by decide +kernel

def cycle50 : CycleData (Fin 15) (Fin 10) := ⟨7,![1,7,5,6,14,13,12,11,2],![0,4,3,2,7,9,6,8,5]⟩

lemma valid50 : cycle50.Valid src dst := by decide +kernel

def cycle51 : CycleData (Fin 15) (Fin 10) := ⟨7,![1,7,8,12,4,3,6,10,2],![0,4,3,8,6,1,2,7,5]⟩

lemma valid51 : cycle51.Valid src dst := by decide +kernel

def cycle52 : CycleData (Fin 15) (Fin 10) := ⟨7,![1,9,13,4,3,5,8,11,2],![0,4,9,6,1,2,3,8,5]⟩

lemma valid52 : cycle52.Valid src dst := by decide +kernel

def cycle53 : CycleData (Fin 15) (Fin 10) := ⟨7,![1,9,13,12,8,5,6,10,2],![0,4,9,6,8,3,2,7,5]⟩

lemma valid53 : cycle53.Valid src dst := by decide +kernel

def cycle54 : CycleData (Fin 15) (Fin 10) := ⟨7,![1,9,14,6,3,4,12,11,2],![0,4,9,7,2,1,6,8,5]⟩

lemma valid54 : cycle54.Valid src dst := by decide +kernel

def cycle55 : CycleData (Fin 15) (Fin 10) := ⟨7,![3,5,7,9,14,10,11,12,4],![1,2,3,4,9,7,5,8,6]⟩

lemma valid55 : cycle55.Valid src dst := by decide +kernel

def cycle56 : CycleData (Fin 15) (Fin 10) := ⟨7,![3,6,10,11,8,7,9,13,4],![1,2,7,5,8,3,4,9,6]⟩

lemma valid56 : cycle56.Valid src dst := by decide +kernel

def cycles : Fin 57 → CycleData (Fin 15) (Fin 10)
  | 0 => cycle0
  | 1 => cycle1
  | 2 => cycle2
  | 3 => cycle3
  | 4 => cycle4
  | 5 => cycle5
  | 6 => cycle6
  | 7 => cycle7
  | 8 => cycle8
  | 9 => cycle9
  | 10 => cycle10
  | 11 => cycle11
  | 12 => cycle12
  | 13 => cycle13
  | 14 => cycle14
  | 15 => cycle15
  | 16 => cycle16
  | 17 => cycle17
  | 18 => cycle18
  | 19 => cycle19
  | 20 => cycle20
  | 21 => cycle21
  | 22 => cycle22
  | 23 => cycle23
  | 24 => cycle24
  | 25 => cycle25
  | 26 => cycle26
  | 27 => cycle27
  | 28 => cycle28
  | 29 => cycle29
  | 30 => cycle30
  | 31 => cycle31
  | 32 => cycle32
  | 33 => cycle33
  | 34 => cycle34
  | 35 => cycle35
  | 36 => cycle36
  | 37 => cycle37
  | 38 => cycle38
  | 39 => cycle39
  | 40 => cycle40
  | 41 => cycle41
  | 42 => cycle42
  | 43 => cycle43
  | 44 => cycle44
  | 45 => cycle45
  | 46 => cycle46
  | 47 => cycle47
  | 48 => cycle48
  | 49 => cycle49
  | 50 => cycle50
  | 51 => cycle51
  | 52 => cycle52
  | 53 => cycle53
  | 54 => cycle54
  | 55 => cycle55
  | _ => cycle56

lemma cycles_valid (i : Fin 57) : (cycles i).Valid src dst := by
  fin_cases i
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
  · exact valid12
  · exact valid13
  · exact valid14
  · exact valid15
  · exact valid16
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
  · exact valid21
  · exact valid22
  · exact valid23
  · exact valid24
  · exact valid25
  · exact valid26
  · exact valid27
  · exact valid28
  · exact valid29
  · exact valid30
  · exact valid31
  · exact valid32
  · exact valid33
  · exact valid34
  · exact valid35
  · exact valid36
  · exact valid37
  · exact valid38
  · exact valid39
  · exact valid40
  · exact valid41
  · exact valid42
  · exact valid43
  · exact valid44
  · exact valid45
  · exact valid46
  · exact valid47
  · exact valid48
  · exact valid49
  · exact valid50
  · exact valid51
  · exact valid52
  · exact valid53
  · exact valid54
  · exact valid55
  · exact valid56

#check cycles_valid

def edges (i : Fin 57) : Finset (Fin 15) := (cycles i).support

lemma edges_circuit (i : Fin 57) : Circuit code (edges i) :=
  CycleData.circuit (cycles_valid i)

lemma src_ne_dst : ∀ i, src i ≠ dst i := by decide

#print axioms cycles_valid

end Erdos184Work.PetersenBase


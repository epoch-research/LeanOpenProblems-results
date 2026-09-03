import Submission.PureSevenMasks
namespace Erdos184Work.PureSevenFactor
open PureSevenRowModel PureSevenProjectionNumbers PureSevenMasks
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
def repIndex : Fin 13 → Fin 6 → Fin 12 := ![![0,1,6,1,8,1],![0,1,6,4,3,7],![0,1,6,4,3,11],![0,1,8,0,3,11],![0,1,8,1,3,11],![0,1,8,1,8,1],![0,1,9,0,2,9],![0,1,9,2,10,3],![0,1,9,2,10,9],![0,2,6,0,5,10],![0,2,6,4,5,11],![0,2,7,0,1,11],![0,3,7,0,1,11]]
def repRows (r : Fin 13) : PureSixRowModel0.Rows := PureSixRowModel0.rows (repIndex r 0) (repIndex r 1) (repIndex r 2) (repIndex r 3) (repIndex r 4) (repIndex r 5)
def lift0 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift0_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift0 (enc6_0 q) e = q := by decide +kernel
def lift1 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift1_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift1 (enc6_1 q) e = q := by decide +kernel
def lift2 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift2_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift2 (enc6_2 q) e = q := by decide +kernel
def lift3 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift3_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift3 (enc6_3 q) e = q := by decide +kernel
def lift4 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift4_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift4 (enc6_4 q) e = q := by decide +kernel
def lift5 : Fin 12 → Fin 5 → Fin 60 := ![![0,1,4,18,59],![2,3,5,19,51],![6,7,10,20,57],![8,9,11,21,36],![12,13,16,22,48],![14,15,17,23,32],![24,25,28,38,58],![26,27,29,39,50],![30,31,33,40,55],![34,35,37,41,44],![42,43,45,52,56],![46,47,49,53,54]]
lemma lift5_complete : ∀ q : Fin 60, ∃ e : Fin 5, lift5 (enc6_5 q) e = q := by decide +kernel
#check lift5_complete

def expanded (r : Fin 13) (e0 : Fin 5) (e1 : Fin 5) (e2 : Fin 5) (e3 : Fin 5) (e4 : Fin 5) (e5 : Fin 5) (q6 : Fin 60) : Rows := rows (lift0 (repIndex r 0) e0) (lift1 (repIndex r 1) e1) (lift2 (repIndex r 2) e2) (lift3 (repIndex r 3) e3) (lift4 (repIndex r 4) e4) (lift5 (repIndex r 5) e5) q6
lemma factor (q : Rows) (r : Fin 13) (h : project6 q = repRows r) :
    ∃ e0 e1 e2 e3 e4 e5 : Fin 5, q = expanded r e0 e1 e2 e3 e4 e5 (q 6) := by
  have h0 := congrArg (fun z : PureSixRowModel0.Rows => (z 0).val) h
  change (enc6_0 (q 0)).val = (repIndex r 0).val at h0
  have he0 : enc6_0 (q 0) = repIndex r 0 := Fin.ext h0
  obtain ⟨e0,hl0⟩ := lift0_complete (q 0)
  rw [he0] at hl0
  have h1 := congrArg (fun z : PureSixRowModel0.Rows => (z 1).val) h
  change (enc6_1 (q 1)).val = (repIndex r 1).val at h1
  have he1 : enc6_1 (q 1) = repIndex r 1 := Fin.ext h1
  obtain ⟨e1,hl1⟩ := lift1_complete (q 1)
  rw [he1] at hl1
  have h2 := congrArg (fun z : PureSixRowModel0.Rows => (z 2).val) h
  change (enc6_2 (q 2)).val = (repIndex r 2).val at h2
  have he2 : enc6_2 (q 2) = repIndex r 2 := Fin.ext h2
  obtain ⟨e2,hl2⟩ := lift2_complete (q 2)
  rw [he2] at hl2
  have h3 := congrArg (fun z : PureSixRowModel0.Rows => (z 3).val) h
  change (enc6_3 (q 3)).val = (repIndex r 3).val at h3
  have he3 : enc6_3 (q 3) = repIndex r 3 := Fin.ext h3
  obtain ⟨e3,hl3⟩ := lift3_complete (q 3)
  rw [he3] at hl3
  have h4 := congrArg (fun z : PureSixRowModel0.Rows => (z 4).val) h
  change (enc6_4 (q 4)).val = (repIndex r 4).val at h4
  have he4 : enc6_4 (q 4) = repIndex r 4 := Fin.ext h4
  obtain ⟨e4,hl4⟩ := lift4_complete (q 4)
  rw [he4] at hl4
  have h5 := congrArg (fun z : PureSixRowModel0.Rows => (z 5).val) h
  change (enc6_5 (q 5)).val = (repIndex r 5).val at h5
  have he5 : enc6_5 (q 5) = repIndex r 5 := Fin.ext h5
  obtain ⟨e5,hl5⟩ := lift5_complete (q 5)
  rw [he5] at hl5
  refine ⟨e0,e1,e2,e3,e4,e5,?_⟩
  funext i
  fin_cases i
  · exact hl0.symm
  · exact hl1.symm
  · exact hl2.symm
  · exact hl3.symm
  · exact hl4.symm
  · exact hl5.symm
  · rfl
#check factor

def CompleteAt (r : Fin 13) (e0 : Fin 5) : Prop :=
  ∀ e1 e2 e3 e4 e5 : Fin 5, commonMask (expanded r e0 e1 e2 e3 e4 e5 0) = 0
instance (r : Fin 13) (e0 : Fin 5) : Decidable (CompleteAt r e0) := by
  unfold CompleteAt
  infer_instance

end Erdos184Work.PureSevenFactor

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


end Erdos184Work.PureSevenFactor

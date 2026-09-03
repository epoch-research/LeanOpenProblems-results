import Submission.PureSixDoubleCheck00
import Submission.PureSixDoubleCheck01
import Submission.PureSixDoubleCheck02
import Submission.PureSixDoubleCheck03
import Submission.PureSixDoubleCheck04
import Submission.PureSixDoubleCheck05
import Submission.PureSixDoubleCheck06
import Submission.PureSixDoubleCheck07
import Submission.PureSixDoubleCheck08
import Submission.PureSixDoubleCheck09
import Submission.PureSixDoubleCheck10
import Submission.PureSixDoubleCheck11
import Submission.PureSixDoubleCheck12
import Submission.PureSixDoubleCheck13
import Submission.PureSixDoubleCheck14
import Submission.PureSixDoubleCheck15
import Submission.PureSixDoubleCheck16
import Submission.PureSixDoubleCheck17
import Submission.PureSixDoubleCheck18
import Submission.PureSixDoubleCheck19
import Submission.PureSixDoubleCheck20
import Submission.PureSixDoubleCheck21
import Submission.PureSixDoubleCheck22
import Submission.PureSixDoubleCheck23
import Submission.PureSixDoubleCheck24
import Submission.PureSixDoubleCheck25
import Submission.PureSixDoubleCheck26
import Submission.PureSixDoubleCheck27
import Submission.PureSixDoubleCheck28
import Submission.PureSixDoubleCheck29
import Submission.PureSixDoubleCheck30
import Submission.PureSixDoubleCheck31

/-! Assembly of the exact six-color numerical classification. -/
namespace Erdos184Work.PureSixDoublePatterns
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma table_correct (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4
  · exact check0 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check1 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check2 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check3 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check5 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check6 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check7 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check8 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check9 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check10 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check11 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check12 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check13 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check14 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check15 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check16 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check17 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check18 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check19 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check20 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check21 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check22 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check23 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check24 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check25 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check26 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check27 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check28 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check29 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check30 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check31 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14

lemma classified (b : Fin 15 → Bool) (hb : Admissible b) :
    ∃ k : Fin 5, ∃ p : Equiv.Perm (Fin 6), ∀ i j,
      between b (p i) (p j) = between (representative k) i j := by
  have he : b = ![b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] := by
    funext i
    fin_cases i <;> rfl
  have ht := table_correct (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)
  rw [← he] at ht
  exact ⟨(normalizer b).1,Equiv.ofBijective (permutations (normalizer b).2)
    (permutations_bijective _),ht hb⟩
#print axioms classified
end Erdos184Work.PureSixDoublePatterns

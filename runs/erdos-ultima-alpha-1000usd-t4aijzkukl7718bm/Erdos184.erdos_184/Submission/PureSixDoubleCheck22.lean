import Submission.PureSixDoubleBase
namespace Erdos184Work.PureSixDoublePatterns
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check22_part0 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,false,true,true,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,false,true,true,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,false,true,true,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,false,true,true,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,false,true,true,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check22_part1 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,false,true,true,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,false,true,true,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,false,true,true,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,false,true,true,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,false,true,true,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check22_part2 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,false,true,true,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,false,true,true,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,false,true,true,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,false,true,true,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,false,true,true,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check22_part3 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,false,true,true,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,false,true,true,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,false,true,true,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,false,true,true,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,false,true,true,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check22 (b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,false,true,true,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,false,true,true,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,false,true,true,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,false,true,true,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,false,true,true,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  cases b5 <;> cases b6
  · exact check22_part0 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check22_part1 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check22_part2 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check22_part3 b7 b8 b9 b10 b11 b12 b13 b14
#print axioms check22
end Erdos184Work.PureSixDoublePatterns

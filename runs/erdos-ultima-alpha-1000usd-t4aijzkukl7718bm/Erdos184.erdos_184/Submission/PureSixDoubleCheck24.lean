import Submission.PureSixDoubleBase
namespace Erdos184Work.PureSixDoublePatterns
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check24_part0 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,true,false,false,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,true,false,false,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,true,false,false,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,true,false,false,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,true,false,false,false,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check24_part1 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,true,false,false,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,true,false,false,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,true,false,false,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,true,false,false,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,true,false,false,false,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check24_part2 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,true,false,false,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,true,false,false,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,true,false,false,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,true,false,false,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,true,false,false,false,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check24_part3 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,true,false,false,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,true,false,false,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,true,false,false,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,true,false,false,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,true,false,false,false,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check24 (b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![true,true,false,false,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![true,true,false,false,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![true,true,false,false,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![true,true,false,false,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![true,true,false,false,false,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  cases b5 <;> cases b6
  · exact check24_part0 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check24_part1 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check24_part2 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check24_part3 b7 b8 b9 b10 b11 b12 b13 b14
#print axioms check24
end Erdos184Work.PureSixDoublePatterns
